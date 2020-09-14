"""Module containing functions to be called inside the verified service. This provides a function to set up the
consumption thread (initialising verification) and a function to insert events into the consumption queue. """

import datetime
import json
import os
import pickle
import threading
import traceback

# this differs between versions...
from Queue import Queue
import requests
from VyPR.SCFG.construction import CFGEdge, CFGVertex
from VyPR.QueryBuilding import *
from VyPR.monitor_synthesis import formula_tree
from VyPR.monitor_synthesis.formula_tree import *
from VyPR.verdict_reports import VerdictReport
import VyPR.config

def VIS_FORMULA_TO_HTML(formula_structure, atoms_list):
    """
    Construct formula HTML for visualisation
    """
    """
    Remember old representation functions that we can reassign.
    """
    StaticState__repr__ = StaticState.__repr__
    StaticTransition__repr__ = StaticTransition.__repr__
    TransitionDurationInInterval__repr__ = TransitionDurationInInterval.__repr__

    """
    Set HTML representation functions.
    """

    StaticState.__repr__ = \
        lambda object: """<span class="tooltip">Bind each event satisfying changes(%s) to the variable %s.</span>
        %s = changes(%s)""" % \
                       (object._name_changed, object._bind_variable_name, object._bind_variable_name,
                        object._name_changed)

    StaticTransition.__repr__ = \
        lambda object: """<span class="tooltip">Bind each event satisfying calls(%s) to the variable %s.</span>
        %s = calls(%s)""" % \
                       (
                       object._operates_on, object._bind_variable_name, object._bind_variable_name, object._operates_on)

    # StateValueInInterval.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>._in(%s)
    #         </span>""" % (atoms_list.index(Atom), Atom._state, Atom._name, Atom._interval)
    #
    # StateValueInOpenInterval.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>._in(%s)
    #         </span>""" % (atoms_list.index(Atom), Atom._state, Atom._name, Atom._interval)
    #
    # StateValueEqualTo.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>.equals(%s)
    #         </span>""" % (atoms_list.index(Atom), Atom._state, Atom._name, Atom._value)
    #
    # StateValueTypeEqualTo.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>.type().equals(%s)
    #         </span>""" % (atoms_list.index(Atom), Atom._state, Atom._name, Atom._value)
    #
    # StateValueEqualToMixed.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>.equals(
    #         <span class="subatom" subatom-index="1">%s(%s)</span>)
    #         </span>""" % (atoms_list.index(Atom), Atom._lhs, Atom._lhs_name, Atom._rhs, Atom._rhs_name)
    #
    # StateValueLengthInInterval.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s(%s)</span>.length()._in(%s)
    #         </span>""" % (atoms_list.index(Atom), Atom._state, Atom._name, Atom._interval)

    TransitionDurationInInterval.__repr__ = \
        lambda Atom: """<span class="atom" atom-index="%i">
            <div class="tooltip">Constraint the duration of %s.</div>
            <span class="subatom" subatom-index="0">%s</span>.duration()._in(%s)
            </span>""" % (atoms_list.index(Atom), Atom._transition, Atom._transition, Atom._interval)

    # TransitionDurationLessThanTransitionDurationMixed.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s</span>.duration() <
    #         <span class="subatom" subatom-index="1">%s</span>.duration()
    #         </span>""" % (atoms_list.index(Atom), Atom._lhs, Atom._rhs)
    #
    # TransitionDurationLessThanStateValueMixed.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s</span>.duration() <
    #         <span class="subatom" subatom-index="1">%s(%s) </span>
    #         </span>""" % (atoms_list.index(Atom), Atom._lhs, Atom._rhs, Atom._rhs_name)
    #
    # TransitionDurationLessThanStateValueLengthMixed.__repr__ = \
    #     lambda Atom: """<span class="atom" atom-index="%i">
    #         <span class="subatom" subatom-index="0">%s</span>.duration() <
    #         <span class="subatom" subatom-index="1">%s(%s)</span>.length()
    #         </span>""" % (atoms_list.index(Atom), Atom._lhs, Atom._rhs, Atom._rhs_name)
    #
    TimeBetweenInInterval.__repr__ = \
        lambda Atom: """<span class="atom" atom-index="%i">timeBetween(
            <div class="tooltip">Constrain the time taken to reach %s from %s.</div>
            <span class="subatom" subatom-index="0">%s</span>,
            <span class="subatom" subatom-index="1">%s</span>)._in(%s)
            </span> """ % (atoms_list.index(Atom), Atom._rhs, Atom._lhs, Atom._lhs, Atom._rhs, Atom._interval)

    TimeBetweenInOpenInterval.__repr__ = \
        lambda Atom: """<span class="atom" atom-index="%i">timeBetween(
            <div class="tooltip">Constrain the time taken to reach %s from %s.</div>
            <span class="subatom" subatom-index="0">%s</span>,
            <span class="subatom" subatom-index="1">%s</span>)._in(%s)
            </span> """ % (atoms_list.index(Atom), Atom._rhs, Atom._lhs, Atom._lhs, Atom._rhs, str(Atom._interval))
    #
    # LogicalAnd.__repr__ = \
    #     lambda object: ('land(%s' % (object.operands[0])) + (', %s' % str for str in object.operands[1:]) + ')'
    #
    # LogicalOr.__repr__ = \
    #     lambda object: ('lor(%s' % (object.operands[0])) + (', %s' % str for str in object.operands[1:]) + ')'
    #
    # LogicalNot.__repr__ = \
    #     lambda object: 'lnot(%s)' % object.operand

    """
    Derive formula HTML
    """
    atom_str = str(formula_structure.get_formula_instance())
    bind_var = formula_structure.bind_variables

    spec = ''
    vars = ''

    # vars will save a list of variables as "x, y, z" - used later in lambda
    # spec begins with Forall(...) - each variable generates one of these
    for (n, var) in enumerate(bind_var.items()):
        atom_str = atom_str.replace(str(var[1]), var[0], 1)
        if spec:
            vars += ", "
        spec += '<div class="list-group-item-text code" id="bind-variable-name-%s'\
                '">Forall(<span class="variable-def" variable="%i">%s</span>).\ </div>' % (var[0], n, var[1])
        vars += var[0]

    for var in bind_var.items():
        atom_str = atom_str.replace(str(var[1]), var[0])

    # finally, add the condition stored in atom_str to the specification
    spec += """<div class="list-group-item-text code">Check( </div>
                <div class="list-group-item-text code">&nbsp;&nbsp;lambda %s : ( </div>
                <div class="list-group-item-text code">&nbsp;&nbsp;&nbsp;&nbsp; %s </div>
                <div class="list-group-item-text code">&nbsp;&nbsp;) </div>
                <div class="list-group-item-text code">)</div>""" % (vars, atom_str)

    """
    Reset representation functions.
    """
    StaticState.__repr__ = StaticState__repr__
    StaticTransition.__repr__ = StaticTransition__repr__
    TransitionDurationInInterval.__repr__ = TransitionDurationInInterval__repr__

    return bind_var.keys(), spec


def SEND_VIS_EVENT(action, data):
    """
    Send a new visualisation event to the server.
    :param action:
    :param data:
    :return: True or False based on success of the http request.
    """
    try:
        print("Sending visualisation event of type '%s' with data '%s'..." % (action, data))
        requests.post(
            os.path.join(VyPR.config.VERDICT_SERVER_URL, "event_stream/add/monitoring/"),
            data = json.dumps({
                "action" : action,
                "data" : json.dumps(data),
                "time_added" : datetime.datetime.now().isoformat()
            })
        )
        print("Visualisation event sent!")
        return True
    except:
        traceback.print_exc()
        return False


class MonitoringLog(object):
    """
    Class to handle monitoring logging.
    """

    def __init__(self, logs_to_stdout):
        self.logs_to_stdout = logs_to_stdout
        # check for log directory - create it if it doesn't exist
        if not (os.path.isdir("vypr_monitoring_logs")):
            os.mkdir("vypr_monitoring_logs")
        self.log_file_name = "vypr_monitoring_logs/%s" \
                             % str(datetime.datetime.utcnow()). \
                                 replace(" ", "_").replace(":", "_").replace(".", "_").replace("-", "_")
        self.handle = None

    def start_logging(self):
        # open the log file in append mode
        self.handle = open(self.log_file_name, "a")

    def end_logging(self):
        self.handle.close()

    def log(self, message):
        if self.handle:
            message = "[VyPR monitoring - %s] %s" % (str(datetime.datetime.utcnow()), message)
            self.handle.write("%s\n" % message)
            # flush the contents of the file to disk - this way we get a log even with an unhandled exception
            self.handle.flush()
            if self.logs_to_stdout:
                print(message)


def to_timestamp(obj):
    if type(obj) is datetime.datetime:
        return obj.isoformat()
    elif type(obj) is datetime.timedelta:
        return obj.total_seconds()
    else:
        return obj


# set up logging variable
vypr_logger = None


def vypr_output(string):
    global vypr_logger
    if VyPR.config.VYPR_OUTPUT_VERBOSE:
        vypr_logger.log(string)


def send_verdict_report(function_name, time_of_call, end_time_of_call, program_path, verdict_report,
                        binding_to_line_numbers, transaction_time, property_hash):
    """
    Send verdict data for a given function call (function name + time of call).
    """
    verdicts = verdict_report.get_final_verdict_report()
    vypr_output("Sending verdicts to server...")

    # first, send function call data - this will also insert program path data
    vypr_output("Function start time was %s" % time_of_call)
    vypr_output("Function end time was %s" % end_time_of_call)

    call_data = {
        "transaction_time": transaction_time.isoformat(),
        "time_of_call": time_of_call.isoformat(),
        "end_time_of_call": end_time_of_call.isoformat(),
        "function_name": function_name,
        "program_path": program_path
    }
    insertion_result = json.loads(requests.post(
        os.path.join(VyPR.config.VERDICT_SERVER_URL, "insert_function_call_data/"),
        data=json.dumps(call_data)
    ).text)

    # second, send verdict data - all data in one request
    # for this, we first build the structure
    # that we'll send over HTTP
    verdict_dict_list = []
    for bind_space_index in verdicts.keys():
        verdict_list = verdicts[bind_space_index]
        for verdict in verdict_list:
            vypr_output("Sending verdict")
            vypr_output(verdict)
            # remember to deal with datetime objects in json serialisation
            verdict_dict = {
                "bind_space_index": bind_space_index,
                "verdict": [
                    verdict[0],
                    verdict[1].isoformat(),
                    verdict[2],
                    verdict[3],
                    verdict[4],
                    verdict[5],
                    verdict[6]
                ],
                "line_numbers": json.dumps(binding_to_line_numbers[bind_space_index])
            }
            verdict_dict_list.append(verdict_dict)

    request_body_dict = {
        "function_call_id": insertion_result["function_call_id"],
        "function_id": insertion_result["function_id"],
        "verdicts": verdict_dict_list,
        "property_hash": property_hash
    }

    # send request
    try:
        requests.post(os.path.join(VyPR.config.VERDICT_SERVER_URL, "register_verdicts/"),
                      data=json.dumps(request_body_dict, default=to_timestamp))
    except Exception as e:
        vypr_output(
            "Something went wrong when sending verdict information to the verdict server.  The verdict information we "
            "tried to send is now lost.")
        import traceback
        vypr_output(traceback.format_exc())

    vypr_output("Verdicts sent.")


def consumption_thread_function(verification_obj):
    # the web service has to be considered as running forever, so the monitoring loop for now should also run forever
    # this needs to be changed for a clean exit
    INACTIVE_MONITORING = False
    continue_monitoring = True
    while continue_monitoring:

        # take top element from the queue
        try:
            top_pair = verification_obj.consumption_queue.get(timeout=1)
        except:
            continue

        if top_pair[0] == "end-monitoring":
            # return from the monitoring function to end the monitoring thread
            vypr_output("Returning from monitoring thread.")
            continue_monitoring = False
            continue

        # if monitoring is inactive, we do nothing with what we consume unless it's a resume message
        if INACTIVE_MONITORING:
            if top_pair[0] == "inactive-monitoring-stop":
                # return from the monitoring function to end the monitoring thread
                vypr_output("Restarting monitoring.  Monitoring thread will still be alive.")
                INACTIVE_MONITORING = False
            continue
        else:
            if top_pair[0] == "inactive-monitoring-start":
                # return from the monitoring function to end the monitoring thread
                vypr_output("Pausing monitoring.  Monitoring thread will still be alive.")
                # turn on inactive monitoring
                INACTIVE_MONITORING = True
                # skip to the next iteration of the consumption loop
                continue
        # if inactive monitoring is off (so monitoring is running), process what we consumed

        vypr_output("Consuming: %s" % str(top_pair))

        property_hash = top_pair[0]

        # remove the property hash and just deal with the rest of the data
        top_pair = top_pair[1:]

        instrument_type = top_pair[0]
        function_name = top_pair[1]

        # get the maps we need for this function
        maps = verification_obj.function_to_maps[function_name][property_hash]
        static_qd_to_monitors = maps.static_qd_to_monitors
        formula_structure = maps.formula_structure
        bindings = maps.binding_space
        program_path = maps.program_path

        verdict_report = maps.verdict_report

        atoms = formula_structure._formula_atoms

        if instrument_type == "function":
            # we've received a point telling us that a function has started or ended
            # for now, we can just process "end" - we reset the contents of the maps
            # that are updated at runtime
            scope_event = top_pair[2]
            if scope_event == "end":

                vypr_output("*" * 50)

                vypr_output("Function '%s' started at time %s has ended at %s."
                            % (function_name, str(maps.latest_time_of_call), str(top_pair[-1])))

                SEND_VIS_EVENT(
                    "function-end",
                    {
                        "function": function_name,
                        "property_hash": property_hash
                    }
                )

                # before resetting the qd -> monitor map, go through it to find monitors
                # that reached a verdict, and register those in the verdict report

                for static_qd_index in static_qd_to_monitors:
                    for monitor in static_qd_to_monitors[static_qd_index]:
                        # check if the monitor has a collapsing atom - only then do we register a verdict
                        if monitor.collapsing_atom:
                            verdict_report.add_verdict(
                                static_qd_index,
                                monitor._formula.verdict,
                                monitor.atom_to_observation,
                                monitor.atom_to_program_path,
                                atoms.index(monitor.collapsing_atom),
                                monitor.collapsing_atom_sub_index,
                                monitor.atom_to_state_dict
                            )

                # everything not here is static data that we need, and should be left
                maps.static_qd_to_monitors = {}

                # generate the verdict report

                report_map = verdict_report.get_final_verdict_report()

                binding_to_line_numbers = {}

                for bind_space_index in report_map.keys():

                    binding = bindings[bind_space_index]

                    binding_to_line_numbers[bind_space_index] = []

                    # for each element of the binding, print the appropriate representation
                    for bind_var in binding:

                        if type(bind_var) is CFGVertex:
                            if bind_var._name_changed == ["loop"]:
                                binding_to_line_numbers[bind_space_index].append(bind_var._structure_obj.lineno)
                            else:
                                binding_to_line_numbers[bind_space_index].append(
                                    bind_var._previous_edge._instruction.lineno)
                        elif type(bind_var) is CFGEdge:
                            binding_to_line_numbers[bind_space_index].append(bind_var._instruction.lineno)

                # send the verdict we send the function name, the time of the function call, the verdict report
                # object, the map of bindings to their line numbers and the date/time of the request the identify it
                # (single threaded...)
                send_verdict_report(
                    function_name,
                    maps.latest_time_of_call,
                    top_pair[-1],
                    maps.program_path,
                    verdict_report,
                    binding_to_line_numbers,
                    verification_obj.transaction_start_time,
                    top_pair[4]
                )

                # reset the verdict report
                maps.verdict_report.reset()

                # reset the function start time for the next time
                maps.latest_time_of_call = None

                # reset the program path
                maps.program_path = []

            elif scope_event == "start":
                vypr_output("Function '%s' has started." % function_name)

                binding_to_line_numbers = {}

                for (bind_space_index, binding) in enumerate(bindings):

                    binding_to_line_numbers[bind_space_index] = []

                    # for each element of the binding, print the appropriate representation
                    for bind_var in binding:

                        if type(bind_var) is CFGVertex:
                            if bind_var._name_changed == ["loop"]:
                                binding_to_line_numbers[bind_space_index].append(bind_var._structure_obj.lineno)
                            else:
                                binding_to_line_numbers[bind_space_index].append(
                                    bind_var._previous_edge._instruction.lineno)
                        elif type(bind_var) is CFGEdge:
                            binding_to_line_numbers[bind_space_index].append(bind_var._instruction.lineno)

                vars, spec = VIS_FORMULA_TO_HTML(formula_structure, atoms)
                SEND_VIS_EVENT(
                    "function-start",
                    {
                        "function": function_name,
                        "property_hash": property_hash,
                        "specification": spec,
                        "variables" : vars,
                        "bindings" : binding_to_line_numbers
                    }
                )

                # remember when the function call started
                maps.latest_time_of_call = top_pair[3]

                vypr_output("Set start time to %s" % maps.latest_time_of_call)

                vypr_output("*" * 50)

        if instrument_type == "trigger":
            # we've received a trigger instrument

            vypr_output("Processing trigger - dealing with monitor instantiation")

            static_qd_index = top_pair[2]
            bind_variable_index = top_pair[3]

            vypr_output("Trigger is for bind variable %i" % bind_variable_index)
            if bind_variable_index == 0:
                vypr_output("Instantiating new, clean monitor")
                # we've encountered a trigger for the first bind variable, so we simply instantiate a new monitor
                new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
                try:
                    static_qd_to_monitors[static_qd_index].append(new_monitor)
                except:
                    static_qd_to_monitors[static_qd_index] = [new_monitor]

                monitor_json, atom_string_list = new_monitor.to_vis_json()
                SEND_VIS_EVENT(
                    "trigger-new-monitor",
                    {
                        "function": function_name,
                        "property_hash": property_hash,
                        "binding_index": static_qd_index,
                        "variable_index": bind_variable_index,
                        "formula_tree" : monitor_json,
                        "atoms" : atom_string_list
                    }
                )
            else:
                vypr_output("Processing existing monitors")
                # we look at the monitors' timestamps, and decide whether to generate a new monitor
                # and copy over existing information, or update timestamps of existing monitors
                new_monitors = []
                subsequences_processed = []
                for monitor in static_qd_to_monitors[static_qd_index]:
                    # check if the monitor's timestamp sequence includes a timestamp for this bind variable
                    vypr_output(
                        "  Processing monitor with timestamp sequence %s" % str(monitor._monitor_instantiation_time))

                    if len(monitor._monitor_instantiation_time) == bind_variable_index + 1:
                        if monitor._monitor_instantiation_time[:bind_variable_index] in subsequences_processed:
                            # the same subsequence might have been copied and extended multiple times
                            # we only care about one
                            continue
                        else:
                            vypr_output("Processing %s" % str(monitor._monitor_instantiation_time[:bind_variable_index]))
                            subsequences_processed.append(monitor._monitor_instantiation_time[:bind_variable_index])
                            # construct new monitor
                            vypr_output("    Instantiating new monitor with modified timestamp sequence")
                            # instantiate a new monitor using the timestamp subsequence excluding the current bind
                            # variable and copy over all observation, path and state information

                            old_instantiation_time = list(monitor._monitor_instantiation_time)
                            updated_instantiation_time = tuple(
                                old_instantiation_time[:bind_variable_index] + [datetime.datetime.utcnow()])
                            new_monitor = formula_tree.new_monitor(formula_structure.get_formula_instance())
                            new_monitors.append(new_monitor)

                            # copy timestamp sequence, observation, path and state information
                            new_monitor._monitor_instantiation_time = updated_instantiation_time

                            # iterate through the observations stored by the previous monitor
                            # for bind variables before the current one and use them to update the new monitor
                            for atom_index in monitor._state._state:
                                atom = atoms[atom_index]
                                if not (type(atom) is formula_tree.LogicalNot):
                                    if (formula_structure._bind_variables.index(
                                            get_base_variable(atom)) < bind_variable_index
                                            and not (monitor._state._state[atom] is None)):
                                        if monitor._state._state[atom] == True:
                                            new_monitor.check_optimised(atom)
                                        elif monitor._state._state[atom] == False:
                                            new_monitor.check_optimised(formula_tree.lnot(atom))

                                        #atom_index = atoms.index(atom)

                                        for sub_index in monitor.atom_to_observation[atom_index].keys():
                                            new_monitor.atom_to_observation[atom_index][sub_index] = \
                                                monitor.atom_to_observation[atom_index][sub_index]

                                        for sub_index in monitor.atom_to_program_path[atom_index].keys():
                                            new_monitor.atom_to_program_path[atom_index][sub_index] = \
                                                monitor.atom_to_program_path[atom_index][sub_index]

                                        for sub_index in monitor.atom_to_state_dict[atom_index].keys():
                                            new_monitor.atom_to_state_dict[atom_index][sub_index] = \
                                                monitor.atom_to_state_dict[atom_index][sub_index]

                            monitor_json, atom_string_list = new_monitor.to_vis_json()
                            SEND_VIS_EVENT(
                                "trigger-new-monitor",
                                {
                                    "function": function_name,
                                    "property_hash": property_hash,
                                    "binding_index": static_qd_index,
                                    "observed_values" : new_monitor.atom_to_observation,
                                    "variable_index": bind_variable_index,
                                    "formula_tree": monitor_json,
                                    "atoms" : atom_string_list
                                }
                            )

                    elif len(monitor._monitor_instantiation_time) == bind_variable_index:
                        vypr_output("    Updating existing monitor timestamp sequence")
                        # extend the monitor's timestamp sequence
                        tmp_sequence = list(monitor._monitor_instantiation_time)
                        tmp_sequence.append(datetime.datetime.utcnow())
                        monitor._monitor_instantiation_time = tuple(tmp_sequence)

                # add the new monitors
                static_qd_to_monitors[static_qd_index] += new_monitors

        if instrument_type == "path":
            # we've received a path recording instrument
            # append the branching condition to the program path encountered so far for this function.
            program_path.append(top_pair[2])

        if instrument_type == "instrument":

            static_qd_indices = top_pair[2]
            atom_index = top_pair[3]
            atom_sub_index = top_pair[4]
            instrumentation_point_db_ids = top_pair[5]
            observation_time = top_pair[6]
            observation_end_time = top_pair[7]
            observed_value = top_pair[8]
            thread_id = top_pair[9]
            try:
                state_dict = top_pair[10]
            except:
                # instrument isn't from a transition measurement
                state_dict = None

            vypr_output("Consuming data from an instrument in thread %i" % thread_id)

            lists = zip(static_qd_indices, instrumentation_point_db_ids)

            for values in lists:

                static_qd_index = values[0]
                instrumentation_point_db_id = values[1]

                vypr_output("Binding space index : %i" % static_qd_index)
                vypr_output("Atom index : %i" % atom_index)
                vypr_output("Atom sub index : %i" % atom_sub_index)
                vypr_output("Instrumentation point db id : %i" % instrumentation_point_db_id)
                vypr_output("Observation time : %s" % str(observation_time))
                vypr_output("Observation end time : %s" % str(observation_end_time))
                vypr_output("Observed value : %s" % observed_value)
                vypr_output("State dictionary : %s" % str(state_dict))

                instrumentation_atom = atoms[atom_index]

                SEND_VIS_EVENT(
                    "receive-measurement",
                    {
                        "function": function_name,
                        "property_hash": property_hash,
                        "binding_index": static_qd_index,
                        "atom_index" : atom_index,
                        "atom_string" : str(atoms[atom_index]),
                        "atom_sub_index" : atom_sub_index,
                        "observation_start_time" : observation_time.isoformat(),
                        "observation_end_time": observation_end_time.isoformat(),
                        "observed_value" : json.dumps(
                            observed_value,
                            default=lambda obj : str(obj) if type(obj) is datetime.datetime else obj
                        ),
                        "path" : {
                            "instrumentation_point_db_id" : instrumentation_point_db_id,
                            "path_condition_sequence" : program_path
                        }
                    }
                )

                # update all monitors associated with static_qd_index
                if static_qd_to_monitors.get(static_qd_index):
                    for (n, monitor) in enumerate(static_qd_to_monitors[static_qd_index]):

                        # check the initial verdict so we know if a new verdict has been reached for visualisation
                        initial_verdict = monitor._formula.verdict

                        # checking for previous observation of the atom is done by the monitor's internal logic
                        monitor.process_atom_and_value(instrumentation_atom, observation_time, observation_end_time,
                                                       observed_value, atom_index, atom_sub_index,
                                                       inst_point_id=instrumentation_point_db_id,
                                                       program_path=len(program_path), state_dict=state_dict)

                        if initial_verdict != monitor._formula.verdict:
                            # if a verdict has been set for the entire monitor
                            SEND_VIS_EVENT(
                                "collapse-monitor",
                                {
                                    "function": function_name,
                                    "property_hash": property_hash,
                                    "binding_index": static_qd_index,
                                    "formula_tree_index" : n,
                                    "verdict" : monitor._formula.verdict
                                }
                            )

        # set the task as done
        verification_obj.consumption_queue.task_done()

        vypr_output("Consumption finished.")

        vypr_output("=" * 100)

    # if we reach this point, the monitoring thread is ending
    vypr_logger.end_logging()


class PropertyMapGroup(object):
    """
    Groups together all the maps needed for verification of a single run of a single function, wrt a single property.
    """

    def __init__(self, module_name, function_name, property_hash):
        self._function_name = function_name
        self._property_hash = property_hash

        # read in binding spaces
        with open(os.path.join(VyPR.config.PROJECT_ROOT, "binding_spaces/module-%s-function-%s-property-%s.dump") % \
                  (module_name.replace(".", "-"), function_name.replace(":", "-"), property_hash), "rb") as h:
            binding_space_dump = h.read()

        # read in index hash map
        with open(os.path.join(VyPR.config.PROJECT_ROOT, "index_hash/module-%s-function-%s.dump") % \
                  (module_name.replace(".", "-"), function_name.replace(":", "-")), "rb") as h:
            index_to_hash_dump = h.read()

        inst_configuration = read_configuration("vypr.config")

        # get the specification file name
        verification_conf_file = inst_configuration.get("specification_file") \
            if inst_configuration.get("specification_file") else "verification_conf.py"

        # reconstruct formula structure
        # there's probably a better way to do this
        # exec("".join(open(verification_conf_file, "r").readlines()))

        try:
            from VyPR_queries_with_imports import verification_conf
        except ImportError:
            print("Query file generated by instrumentation couldn't be found.  Run VyPR instrumentation first.")
            exit()

        index_to_hash = pickle.loads(index_to_hash_dump)
        property_index = index_to_hash.index(property_hash)

        vypr_output("Queries imported.")

        # might just change the syntax in the verification conf file at some point to use : instead of .
        self.formula_structure = verification_conf[module_name][function_name.replace(":", ".")][property_index]
        self.binding_space = pickle.loads(binding_space_dump)
        self.static_qd_to_monitors = {}
        self.static_bindings_to_monitor_states = {}
        self.static_bindings_to_trigger_points = {}
        self.verdict_report = VerdictReport()
        self.latest_time_of_call = None
        self.program_path = []


def read_configuration(file):
    """
    Read in 'file', parse into an object and return.
    """
    with open(file, "r") as h:
        contents = h.read()

    return json.loads(contents)


class Verification(object):

    def __init__(self):
        """
        Sets up the consumption thread for events from instruments.
        """

        global vypr_logger
        vypr_logger = MonitoringLog(logs_to_stdout=False)
        vypr_logger.start_logging()

        vypr_output("VyPR verification object instantiated...")

        # read configuration file
        inst_configuration = read_configuration("vypr.config")
        VyPR.config.VERDICT_SERVER_URL = inst_configuration.get("verdict_server_url") if inst_configuration.get(
            "verdict_server_url") else "http://localhost:9001/"
        VyPR.config.VYPR_OUTPUT_VERBOSE = inst_configuration.get("verbose") if inst_configuration.get("verbose") else True
        VyPR.config.PROJECT_ROOT = inst_configuration.get("project_root") if inst_configuration.get("project_root") else ""

        self.machine_id = ("%s-" % inst_configuration.get("machine_id")) if inst_configuration.get("machine_id") else ""

        # check if there's an NTP server given that we should use for time
        self.ntp_server = inst_configuration.get("ntp_server")
        if self.ntp_server:
            # set two timestamps - the local time, and the ntp server time, from the same instant
            import ntplib
            client = ntplib.NTPClient()
            try:
                response = client.request(self.ntp_server)
                # set the local start time
                self.local_start_time = datetime.datetime.utcfromtimestamp(response.orig_time)
                # compute the delay due to network latency to reach the ntp server
                adjustment = (response.dest_time - response.orig_time)/2
                # set the ntp start time by subtracting the adjustment from the time given by the ntp server
                # this works because 'adjustment' is approximately the time elapsed
                # between the first time we measure local time and when the ntp server measures its own time
                # so by subtracting this difference we adjust the ntp server time to the same instant
                # as the local time
                self.ntp_start_time = datetime.datetime.utcfromtimestamp(response.tx_time - adjustment)
            except:
                vypr_output("Couldn't set time based on NTP server '%s'." % self.ntp_server)
                print("Couldn't set time based on NTP server '%s'." % self.ntp_server)
                exit()

        # try to connect to the verdict server before we set anything up
        try:
            attempt = requests.get(VyPR.config.VERDICT_SERVER_URL)
            self.initialisation_failure = False
        except Exception:
            vypr_output("Couldn't connect to the verdict server at '%s'.  Initialisation failed." % VERDICT_SERVER_URL)
            self.initialisation_failure = True
            return

    def initialise(self):

        vypr_output("Initialising VyPR alongside service.")

        # we count the transaction start time as the time when VyPR starts up
        self.transaction_start_time = datetime.datetime.utcnow()

        # set up the maps that the monitoring algorithm that the consumption thread runs

        # we need the list of functions that we have instrumentation data from, so read the instrumentation maps
        # directory
        dump_files = filter(lambda filename: ".dump" in filename,
                            os.listdir(os.path.join(VyPR.config.PROJECT_ROOT, "binding_spaces")))
        functions_and_properties = map(lambda function_dump_file: function_dump_file.replace(".dump", ""), dump_files)
        tokens = map(lambda string: string.split("-"), functions_and_properties)

        self.function_to_maps = {}

        for token_chain in tokens:

            start_of_module = token_chain.index("module") + 1
            start_of_function = token_chain.index("function") + 1
            start_of_property = token_chain.index("property") + 1

            module_string = ".".join(token_chain[start_of_module:start_of_function - 1])
            # will need to be modified to support functions that are methods
            # function = ".".join(token_chain[start_of_function:start_of_property-1])
            function = ":".join(token_chain[start_of_function:start_of_property - 1])

            property_hash = token_chain[start_of_property]

            vypr_output("Setting up monitoring state for module/function/property triple %s, %s, %s" % (
                module_string, function, property_hash))

            module_function_string = "%s%s.%s" % (self.machine_id, module_string, function)

            if not (self.function_to_maps.get(module_function_string)):
                self.function_to_maps[module_function_string] = {}
            self.function_to_maps[module_function_string][property_hash] = PropertyMapGroup(module_string, function,
                                                                                            property_hash)

        vypr_output(self.function_to_maps)

        vypr_output("Setting up monitoring thread.")

        # setup consumption queue and store it globally across requests
        self.consumption_queue = Queue()
        # setup consumption thread
        self.consumption_thread = threading.Thread(
            target=consumption_thread_function,
            args=[self]
        )
        self.consumption_thread.start()

        vypr_output("VyPR monitoring initialisation finished.")

    def get_time(self):
        """
        Returns either the machine local time, or the NTP time (using the initial NTP time
        obtained when VyPR started up, so we don't query an NTP server everytime we want to measure time).
        The result is in UTC.
        :return: datetime.datetime object
        """
        if self.ntp_server:
            vypr_output("Getting time based on NTP.")
            current_local_time = datetime.datetime.utcnow()
            # compute the time elapsed since the start
            difference = current_local_time - self.local_start_time
            # add that time to the ntp time obtained at the start
            current_ntp_time = self.ntp_start_time + difference
            return current_ntp_time
        else:
            vypr_output("Getting time based on local machine.")
            return datetime.datetime.utcnow()

    def send_event(self, event_description):
        if not (self.initialisation_failure):
            self.consumption_queue.put(event_description)

    def end_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("Ending VyPR monitoring thread.")
            self.consumption_queue.put(("end-monitoring",))

    def pause_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("Sending monitoring pause message.")
            self.consumption_queue.put(("inactive-monitoring-start",))

    def resume_monitoring(self):
        if not (self.initialisation_failure):
            vypr_output("Sending monitoring resume message.")
            self.consumption_queue.put(("inactive-monitoring-stop",))
