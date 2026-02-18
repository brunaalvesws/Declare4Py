from __future__ import annotations

import pdb
from abc import ABC
from datetime import timedelta
from math import ceil
from typing import List, Optional

from Declare4Py.D4PyEventLog import D4PyEventLog
from Declare4Py.ProcessModels.DeclareModel import DeclareModel
from Declare4Py.ProcessModels.DeclareModel import DeclareModelConditionParserUtility, DeclareModelTemplate
from Declare4Py.Utils.Declare.TraceStates import TraceState
glob = {'__builtins__': None}


class ConstraintChecker:

    def check_trace_conformance(self, trace: dict, decl_model: DeclareModel, consider_vacuity: bool = False,
                                concept_name: str = "concept:name", track_violations: str = "@@index") -> List[CheckerResult]:
        """
        Checks whether the constraints are fulfillment, violation, pendings, activations etc

        Parameters
        ----------
        :param bool consider_vacuity: True means that vacuously satisfied traces are considered as satisfied, violated otherwise
        :param d4pyEventLog trace: log
        :param DeclareModel decl_model: Process mining model
        Args:
            concept_name:
            concept_name:
        """

        # Set containing all constraints that raised SyntaxError in checker functions
        rules = {"vacuous_satisfaction": consider_vacuity}
        error_constraint_set = set()
        model: DeclareModel = decl_model
        trace_results = []
        for idx, constraint in enumerate(model.constraints):
            constraint_str = model.serialized_constraints[idx]
            rules["activation"] = constraint['condition'][0]
            if constraint['template'].supports_cardinality:
                rules["n"] = constraint['n']
            if constraint['template'].is_binary:
                rules["correlation"] = constraint['condition'][1]
            rules["time"] = constraint['condition'][-1]  # time condition is always at last position
            try:
                trace_results.append(TemplateConstraintChecker(trace, True, constraint['activities'], rules,
                                                               concept_name, track_violations).get_template(constraint['template'])())
            except SyntaxError:
                # TODO: use python logger
                if constraint_str not in error_constraint_set:
                    error_constraint_set.add(constraint_str)
                    print('Condition not properly formatted for constraint "' + constraint_str + '".')
        return trace_results

    def constraint_checking_with_support(self, constraint: dict, event_log: D4PyEventLog, consider_vacuity: bool,
                                         min_support: float) -> bool:
        """
        Check wheter a constraint is satisfied in a log up to a given minimum support
        Args:
            consider_vacuity:
            event_log:
            min_support:
            constraint:

        Returns:

        """
        # Fake model composed by a single constraint
        tmp_model = DeclareModel()
        tmp_model.constraints.append(constraint)
        tmp_model.set_constraints()
        sat_ctr = 0

        for i, trace in enumerate(event_log.get_log()):
            trc_res = self.check_trace_conformance(trace, tmp_model, consider_vacuity, event_log.activity_key)
            if not trc_res:  # Occurring when constraint data conditions are formatted bad
                break
            # constraint_str, checker_res = next(iter(trc_res.items()))  # trc_res will always have only one element inside
            checker_res = trc_res[0]
            if checker_res.state == TraceState.SATISFIED:
                sat_ctr += 1
                # If the constraint is already above the minimum support, return it directly
                if sat_ctr / len(event_log.log) >= min_support:
                    return True #constraint_str
            # If there aren't enough more traces to reach the minimum support, return nothing
            if event_log.get_length() - (i + 1) < ceil(event_log.get_length() * min_support) - sat_ctr:
                return False # None
        return False # None

class TemplateConstraintChecker(ABC):

    def __init__(self, traces: dict, completed: bool, activities: List[str], rules: dict,
                 concept_name: str = "concept:name", track_violations: str = "@@index"):
        self.declare_parser_utility = DeclareModelConditionParserUtility()
        self.traces: dict = traces
        self.completed: bool = completed
        self.activities: List[str] = activities
        self.rules: dict = rules
        self.concept_name: str = concept_name
        self.track_violations: str = track_violations

    def get_template(self, template: DeclareModelTemplate):
        """
        We have the classes with each template constraint checker and we invoke them dynamically
        and they check the result on given parameters
        Parameters
        ----------
        template: name of the declared model template
        traces
        completed
        activities: activities of declare model template which should be checked. Can be one or two activities
        rules: dict. conditions of template and 'n' for unary templates which represents 'n' times

        Returns
        -------

        """

        template_checker_name = f"mp{template.templ_str.replace(' ', '')}"
        try:
            return getattr(self, template_checker_name)
        except AttributeError:
            print(f"The checker function for template {template.templ_str} has not been implemented yet.")

    def mpChoice(self) -> CheckerResult:
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        a_or_b_occurs = False
        event_ids = []
        
        for A in self.traces:
            if A[self.concept_name] == self.activities[0] or A[self.concept_name] == self.activities[1]:
                locl = {'A': A, 'T': self.traces[0], 'timedelta': timedelta, 'abs': abs, 'float': float}
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    a_or_b_occurs = True
                    break
        state = None
        if not self.completed and not a_or_b_occurs:
            state = TraceState.POSSIBLY_VIOLATED
        elif self.completed and not a_or_b_occurs:
            state = TraceState.VIOLATED
        elif a_or_b_occurs:
            state = TraceState.SATISFIED
            event_ids = None

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_ids)

    def mpExclusiveChoice(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        a_occurs = False
        b_occurs = False
        
        event_ids = []
        for A in self.traces:
            locl = {'A': A, 'T': self.traces[0], 'timedelta': timedelta, 'abs': abs, 'float': float}
            if not a_occurs and A[self.concept_name] == self.activities[0]:
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    a_occurs = True
                    event_ids.append(A[self.track_violations])
            if not b_occurs and A[self.concept_name] == self.activities[1]:
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    b_occurs = True
                    event_ids.append(A[self.track_violations])
            if a_occurs and b_occurs:
                break
        state = None
        if not self.completed and (not a_occurs and not b_occurs):
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and (a_occurs ^ b_occurs):
            event_ids = None
            state = TraceState.POSSIBLY_SATISFIED
        elif (a_occurs and b_occurs) or (self.completed and (not a_occurs and not b_occurs)):
            state = TraceState.VIOLATED
        elif self.completed and (a_occurs ^ b_occurs):
            event_ids = None
            state = TraceState.SATISFIED

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_ids)

    """
        mp-existence constraint checker
        Description: The future constraining constraint existence(n, a) indicates that
        event a must occur at least n-times in the trace.
    """
    def mpExistence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        
        event_ids = []
        num_activations = 0
        for A in self.traces:
            if A[self.concept_name] == self.activities[0]:
                locl = {'A': A, 'T': self.traces[0], 'timedelta': timedelta, 'abs': abs, 'float': float}
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    num_activations += 1
                    event_ids.append(A[self.track_violations])
                    
        n = self.rules["n"]
        state = None
        if not self.completed and num_activations < n:
            state = TraceState.POSSIBLY_VIOLATED
        elif self.completed and num_activations < n:
            state = TraceState.VIOLATED
        elif num_activations >= n:
            state = TraceState.SATISFIED
            event_ids = None
        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_ids)

    """
        mp-absence constraint checker
        Description: The future constraining constraint absence(n + 1, a) indicates that
        event a may occur at most n − times in the trace.
    """
    def mpAbsence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        event_ids = []
        num_activations = 0
        
        n = self.rules["n"]
        
        for A in self.traces:
            if A[self.concept_name] == self.activities[0]:
                locl = {'A': A, 'T': self.traces[0], 'timedelta': timedelta, 'abs': abs, 'float': float}
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    num_activations += 1
                    if num_activations >= n:
                        event_ids.append(A[self.track_violations])

        state = None
        if not self.completed and num_activations < n:
            state = TraceState.POSSIBLY_SATISFIED
            event_ids = None
        elif num_activations >= n:
            state = TraceState.VIOLATED
        elif self.completed and num_activations < n:
            state = TraceState.SATISFIED
            event_ids = None

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_ids)

    """
        mp-init constraint checker
        Description: The future constraining constraint init(e) indicates
        that event e is the first event that occurs in the trace.
    """
    def mpInit(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])

        state = TraceState.VIOLATED
        event_id = [self.traces[0][self.track_violations]]
        if self.traces[0][self.concept_name] == self.activities[0]:
            locl = {'A': self.traces[0]}
            if eval(activation_rules, glob, locl):
                state = TraceState.SATISFIED
                event_id = None

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_id)

    """
        mp-init constraint checker
        Description: The future constraining constraint init(e) indicates
        that event e is the first event that occurs in the trace.
    """
    def mpEnd(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])

        state = TraceState.VIOLATED
        event_id = [self.traces[-1][self.track_violations]]
        if self.traces[-1][self.concept_name] == self.activities[0]:
            locl = {'A': self.traces[-1]}
            if eval(activation_rules, glob, locl):
                state = TraceState.SATISFIED
                event_id = None

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_id)

    """
        mp-exactly constraint checker
    """
    def mpExactly(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        
        event_ids = []
        num_activations = 0
        for A in self.traces:
            if A[self.concept_name] == self.activities[0]:
                locl = {'A': A, 'T': self.traces[0], 'timedelta': timedelta, 'abs': abs, 'float': float}
                if eval(activation_rules, glob, locl) and eval(time_rule, glob, locl):
                    num_activations += 1
                    event_ids.append(A[self.track_violations])
                    
        n = self.rules["n"]
        state = None
        if not self.completed and num_activations < n:
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_activations == n:
            state = TraceState.POSSIBLY_SATISFIED
            event_ids = None
        elif num_activations > n or (self.completed and num_activations < n):
            state = TraceState.VIOLATED
        elif self.completed and num_activations == n:
            state = TraceState.SATISFIED
            event_ids = None

        return CheckerResult(num_fulfillments=None, num_violations=None, num_pendings=None, num_activations=None,
                             state=state, events_violated=event_ids)

    # mp-responded-existence constraint checker
    # Description:
    # The future constraining and history-based constraint
    # respondedExistence(a, b) indicates that, if event a occurs in the trace
    # then event b occurs in the trace as well.
    # Event a activates the constraint.
    def mpRespondedExistence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        pendings = []
        num_fulfillments = 0
        num_violations = 0
        num_pendings = 0

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}
                if eval(activation_rules, glob, locl):
                    pendings.append(event)

        for event in self.traces:
            if not pendings:
                break

            if event[self.concept_name] == self.activities[1]:
                for A in reversed(pendings):
                    locl = {'A': A, 'T': event, 'timedelta': timedelta, 'abs': abs, 'float': float}
                    if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                        pendings.remove(A)
                        num_fulfillments += 1

        if self.completed:
            num_violations = len(pendings)
        else:
            num_pendings = len(pendings)

        num_activations = num_fulfillments + num_violations + num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        pendings_ids = list(map(lambda x: x[self.track_violations], pendings))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations > 0:
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            pendings_ids = None
        elif self.completed and num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            pendings_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=pendings_ids)

    def mpResponse(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        pendings = []
        num_fulfillments = 0
        num_violations = 0
        num_pendings = 0

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}
                if eval(activation_rules, glob, locl):
                    pendings.append(event)

            if pendings and event[self.concept_name] == self.activities[1]:
                for A in reversed(pendings):
                    locl = {'A': A, 'T': event, 'timedelta': timedelta, 'abs': abs, 'float': float}
                    if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                        pendings.remove(A)
                        num_fulfillments += 1

        if self.completed:
            num_violations = len(pendings)
        else:
            num_pendings = len(pendings)

        num_activations = num_fulfillments + num_violations + num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        pendings_ids = list(map(lambda x: x[self.track_violations], pendings))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_pendings > 0:
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_pendings == 0:
            state = TraceState.POSSIBLY_SATISFIED
            pendings_ids = None
        elif self.completed and num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            pendings_ids = None
            

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=pendings_ids)

    # mp-alternate-response constraint checker
    # Description:
    # The future constraining constraint alternateResponse(a, b) indicates that
    # each time event a occurs in the trace then event b occurs afterwards
    # before event a recurs.
    # Event a activates the constraint.
    def mpAlternateResponse(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        pending = None
        num_activations = 0
        num_fulfillments = 0
        num_pendings = 0
        events_id = []

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}
                if eval(activation_rules, glob, locl):
                    pending = event
                    num_activations += 1
                    events_id.append(event[self.track_violations])

            if event[self.concept_name] == self.activities[1] and pending is not None:
                locl = {'A': pending, 'T': event, 'timedelta': timedelta, 'abs': abs, 'float': float}
                if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                    pending = None
                    num_fulfillments += 1
                    if len(events_id) == 1:
                        events_id = []

        if not self.completed and pending is not None:
            num_pendings = 1

        num_violations = num_activations - num_fulfillments - num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0 and num_pendings > 0:
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0 and num_pendings == 0:
            state = TraceState.POSSIBLY_SATISFIED
            events_id = None
        elif num_violations > 0 or (self.completed and num_pendings > 0):
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0 and num_pendings == 0:
            state = TraceState.SATISFIED
            events_id = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=events_id)

    def mpChainResponse(self):
        """
        The future constraining constraint chain_response(a, b) indicates that, each time event a occurs in the trace,
        event b occurs immediately afterwards. Event a activates the constraint.
        Returns:

        """
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        num_activations = 0
        num_fulfillments = 0
        num_pendings = 0
        pendings_ids = []

        for index, event in enumerate(self.traces):

            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}

                if eval(activation_rules, glob, locl):
                    num_activations += 1
                    pendings_ids.append(event[self.track_violations])

                    if index < len(self.traces) - 1:
                        if self.traces[index + 1][self.concept_name] == self.activities[1]:
                            locl = {'A': event, 'T': self.traces[index + 1], 'timedelta': timedelta, 'abs': abs,
                                    'float': float}
                            if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                                num_fulfillments += 1
                                pendings_ids.remove(event[self.track_violations])
                    else:
                        if not self.completed:
                            num_pendings = 1

        num_violations = num_activations - num_fulfillments - num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0 and num_pendings > 0:
            state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0 and num_pendings == 0:
            state = TraceState.POSSIBLY_SATISFIED
            pendings_ids = None
        elif num_violations > 0 or (self.completed and num_pendings > 0):
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0 and num_pendings == 0:
            state = TraceState.SATISFIED
            pendings_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=pendings_ids)

    def mpPrecedence(self):
        """
        The history-based constraint precedence(a,b) indicates that event b occurs only in the trace, if preceded by a.
        Event b activates the constraint.
        Returns:

        """
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        num_activations = 0
        num_fulfillments = 0
        Ts = []
        activators = []

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                Ts.append(event)

            if event[self.concept_name] == self.activities[1]:
                locl = {'A': event}
                activators.append(event)
                
                if eval(activation_rules, glob, locl):
                    num_activations += 1

                    for T in Ts:
                        locl = {'A': event, 'T': T, 'timedelta': timedelta, 'abs': abs, 'float': float}
                        if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                            num_fulfillments += 1
                            activators.remove(event)
                            break

        num_violations = num_activations - num_fulfillments
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        activators_ids = list(map(lambda x: x[self.track_violations], activators))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            activators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            activators_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations, num_pendings=None,
                             num_activations=num_activations, state=state, events_violated=activators_ids)

    def mpAlternatePrecedence(self):
        """
        The history-based constraint alternatePrecedence(a, b) indicates that each time event b occurs in the trace
        it is preceded by event a and no other event b can recur in between. Event b activates the constraint.
        Returns:

        """
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        num_activations = 0
        num_fulfillments = 0
        activators = []
        Ts = []

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                Ts.append(event)

            if event[self.concept_name] == self.activities[1]:
                locl = {'A': event}
                
                if eval(activation_rules, glob, locl):
                    num_activations += 1
                    activators.append(event)
                    
                    for T in Ts:
                        locl = {'A': event, 'T': T, 'timedelta': timedelta, 'abs': abs, 'float': float}
                        if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                            num_fulfillments += 1
                            activators.remove(event)
                            break
                    Ts = []
        num_violations = num_activations - num_fulfillments
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        activators_ids = list(map(lambda x: x[self.track_violations], activators))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            activators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            activators_ids = None
        
        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations, num_pendings=None,
                             num_activations=num_activations, state=state, events_violated=activators_ids)

    def mpChainPrecedence(self):
        """
        The history-based constraint chain_precedence(a, b) indicates that, each time event b occurs in the trace,
        event a occurs immediately beforehand. Event b activates the constraint.
        Returns:

        """
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        num_activations = 0
        num_fulfillments = 0
        pendings_ids = []

        for index, event in enumerate(self.traces):
            if event[self.concept_name] == self.activities[1]:
                locl = {'A': event}

                if eval(activation_rules, glob, locl):
                    num_activations += 1
                    pendings_ids.append(event[self.track_violations]) 

                    if index != 0 and self.traces[index - 1][self.concept_name] == self.activities[0]:
                        locl = {'A': event, 'T': self.traces[index - 1], 'timedelta': timedelta, 'abs': abs,
                                'float': float}
                        if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                            num_fulfillments += 1
                            pendings_ids.remove(event[self.track_violations])
                            
        num_violations = num_activations - num_fulfillments
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            pendings_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            pendings_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations, num_pendings=None,
                             num_activations=num_activations, state=state, events_violated=pendings_ids)

    def mpNotRespondedExistence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        pendings = []
        event_ids = []
        num_fulfillments = 0
        num_violations = 0
        num_pendings = 0

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}
                if eval(activation_rules, glob, locl):
                    pendings.append(event)

        for event in self.traces:
            if not pendings:
                break

            if event[self.concept_name] == self.activities[1]:
                for A in reversed(pendings):
                    locl = {'A': A, 'T': event, 'timedelta': timedelta, 'abs': abs, 'float': float}
                    if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                        pendings.remove(A)
                        event_ids.append(event[self.track_violations])
                        num_violations += 1

        if self.completed:
            num_fulfillments = len(pendings)
        else:
            num_pendings = len(pendings)

        num_activations = num_fulfillments + num_violations + num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            event_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            event_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=event_ids)

    def mpNotResponse(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        pendings = []
        violators = []
        num_fulfillments = 0
        num_violations = 0
        num_pendings = 0

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}
                if eval(activation_rules, glob, locl):
                    pendings.append(event)

            if pendings and event[self.concept_name] == self.activities[1]:
                for A in reversed(pendings):
                    locl = {'A': A, 'T': event, 'timedelta': timedelta, 'abs': abs, 'float': float}
                    if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                        pendings.remove(A)
                        violators.append(event)
                        num_violations += 1

        if self.completed:
            num_fulfillments = len(pendings)
        else:
            num_pendings = len(pendings)

        num_activations = num_fulfillments + num_violations + num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        violators_ids = list(map(lambda x: x[self.track_violations], violators))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            violators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            violators_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=violators_ids)

    def mpNotPrecedence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])

        num_activations = 0
        num_violations = 0
        Ts = []
        violators = []

        for event in self.traces:
            if event[self.concept_name] == self.activities[0]:
                Ts.append(event)

            if event[self.concept_name] == self.activities[1]:
                locl = {'A': event}

                if eval(activation_rules, glob, locl):
                    num_activations += 1

                    for T in Ts:
                        locl = {'A': event, 'T': T, 'timedelta': timedelta, 'abs': abs, 'float': float}
                        if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                            num_violations += 1
                            violators.append(T)
                            break

        num_fulfillments = num_activations - num_violations
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None
        
        violators_ids = list(map(lambda x: x[self.track_violations], violators))

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            violators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            violators_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations, num_pendings=None,
                             num_activations=num_activations, state=state, events_violated=violators_ids)

    def mpNotChainPrecedence(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        num_activations = 0
        num_violations = 0
        violators_ids = []

        for index, event in enumerate(self.traces):

            if event[self.concept_name] == self.activities[1]:
                locl = {'A': event}

                if eval(activation_rules, glob, locl):
                    num_activations += 1

                    if index != 0 and self.traces[index - 1][self.concept_name] == self.activities[0]:
                        locl = {'A': event, 'T': self.traces[index - 1], 'timedelta': timedelta, 'abs': abs,
                                'float': float}
                        if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                            num_violations += 1
                            violators_ids.append( self.traces[index - 1][self.track_violations])

        num_fulfillments = num_activations - num_violations
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            violators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            violators_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations, num_pendings=None,
                             num_activations=num_activations, state=state,events_violated=violators_ids)

    def mpNotChainResponse(self):
        activation_rules = self.declare_parser_utility.parse_data_cond(self.rules["activation"])
        correlation_rules = self.declare_parser_utility.parse_data_cond(self.rules["correlation"])
        time_rule = self.declare_parser_utility.parse_time_cond(self.rules["time"])
        num_activations = 0
        num_violations = 0
        num_pendings = 0
        
        violators_ids = []

        for index, event in enumerate(self.traces):

            if event[self.concept_name] == self.activities[0]:
                locl = {'A': event}

                if eval(activation_rules, glob, locl):
                    num_activations += 1

                    if index < len(self.traces) - 1:
                        if self.traces[index + 1][self.concept_name] == self.activities[1]:
                            locl = {'A': event, 'T': self.traces[index + 1], 'timedelta': timedelta, 'abs': abs,
                                    'float': float}
                            if eval(correlation_rules, glob, locl) and eval(time_rule, glob, locl):
                                num_violations += 1
                                violators_ids.append(self.traces[index + 1][self.track_violations])
                    else:
                        if not self.completed:
                            num_pendings = 1

        num_fulfillments = num_activations - num_violations - num_pendings
        vacuous_satisfaction = self.rules["vacuous_satisfaction"]
        state = None

        if not vacuous_satisfaction and num_activations == 0:
            if self.completed:
                state = TraceState.VIOLATED
            else:
                state = TraceState.POSSIBLY_VIOLATED
        elif not self.completed and num_violations == 0:
            state = TraceState.POSSIBLY_SATISFIED
            violators_ids = None
        elif num_violations > 0:
            state = TraceState.VIOLATED
        elif self.completed and num_violations == 0:
            state = TraceState.SATISFIED
            violators_ids = None

        return CheckerResult(num_fulfillments=num_fulfillments, num_violations=num_violations,
                             num_pendings=num_pendings, num_activations=num_activations, state=state, events_violated=violators_ids)


class CheckerResult:
    def __init__(self, num_fulfillments: Optional[int], num_violations: Optional[int], num_pendings: Optional[int],
                 num_activations: Optional[int], state: TraceState, events_violated: Optional[List]):
        self.num_fulfillments = num_fulfillments
        self.num_violations = num_violations
        self.num_pendings = num_pendings
        self.num_activations = num_activations
        self.state = state
        self.events_violated = events_violated
