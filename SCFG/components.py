"""
Component classes of an SCFG.
"""
import ast
from VyPR.SCFG.utils import *

class CFGVertex(object):
    """
    This class represents a vertex in a control flow graph.
    """

    def __init__(self, entry=None, path_length=None, structure_obj=None, reference_variables=[]):
        """
        Given the name changed in the state this vertex represents, store it.
        """
        # the distance from the last branching point to this vertex
        self._path_length = path_length
        # structure_obj is so vertices for control-flow such as conditionals and loops have a reference
        # to the ast object that generated them
        self._structure_obj = structure_obj
        if not (entry):
            self._name_changed = []
        else:
            if type(entry) is ast.Assign and type(entry.value) in [ast.Call, ast.Expr]:
                # only works for a single function being called - should make this recursive
                # for complex expressions that require multiple calls
                if type(entry.targets[0]) is ast.Tuple:
                    self._name_changed = list(
                        list(map(get_attr_name_string, entry.targets[0].elts)) + get_function_name_strings(entry)
                    )
                else:
                    self._name_changed = [get_attr_name_string(entry.targets[0])] + get_function_name_strings(entry)
            # TODO: include case where the expression on the right hand side of the assignment is an expression with
            #  a call
            elif type(entry) is ast.AugAssign:
                self._name_changed = [get_attr_name_string(entry.target)] + get_function_name_strings(entry)
            elif type(entry) is ast.Expr and type(entry.value) is ast.Call:
                # if there are reference variables, we include them as possibly changed
                self._name_changed = get_function_name_strings(entry.value) + (
                    reference_variables if len(entry.value.args) > 0 else [])
            elif type(entry) is ast.Assign:
                self._name_changed = [get_attr_name_string(entry.targets[0])]
            elif typ(entry) is ast.AugAssign:
                self._name_changed = [get_attr_name_string(entry.target)]
            elif type(entry) is ast.Return:
                if type(entry.value) is ast.Call:
                    self._name_changed = get_function_name_strings(entry.value)
                else:
                    # nothing else could be changed
                    self._name_changed = []
            elif type(entry) is ast.Raise:
                self._name_changed = [entry.type.func.id]
            elif type(entry) is ast.Pass:
                self._name_changed = ["pass"]
            elif type(entry) is ast.Continue:
                self._name_changed = ["continue"]

        self.edges = []
        self._previous_edge = None

    def add_outgoing_edge(self, edge):
        edge._source_state = self
        self.edges.append(edge)

    def __repr__(self):
        return "<Vertex [%s]>" % (", ".join(self._name_changed))

    def to_vis_json(self):
        line_number = self._previous_edge._instruction.lineno \
            if hasattr(self._previous_edge, "_instruction") and type(self._previous_edge._instruction) is not str \
            else None
        dict_form = {
            "id" : id(self),
            "state_changed" : map(str, self._name_changed),
            "children" : map(id, map(lambda edge : edge._target_state, self.edges)),
            "line_number" : line_number
        }
        return dict_form


class CFGEdge(object):
    """
    This class represents an edge in a control flow graph.
    """

    def __init__(self, condition, instruction=None):
        # the condition has to be copied, otherwise later additions to the condition on the same branch
        # for example, to indicate divergence and convergence of control flow
        # will also be reflected in conditions earlier in the branch
        self._condition = [c for c in condition] if type(condition) is list else condition
        self._instruction = instruction
        self._source_state = None
        self._target_state = None

        if type(self._instruction) is ast.Assign and type(self._instruction.value) in [ast.Call, ast.Expr]:
            # we will have to deal with other kinds of expressions at some point
            if type(self._instruction.targets[0]) is ast.Tuple:
                self._operates_on = list(map(get_attr_name_string,
                                             self._instruction.targets[0].elts) + get_function_name_strings(
                    self._instruction.value))
            else:
                self._operates_on = [get_attr_name_string(self._instruction.targets[0])] + \
                                    get_function_name_strings(self._instruction.value)
        # print(self._operates_on)
        elif type(self._instruction) is ast.Assign and not (type(self._instruction.value) is ast.Call):
            # print("constructed string: ", get_attr_name_string(self._instruction.targets[0]))
            self._operates_on = get_attr_name_string(self._instruction.targets[0])
        elif type(self._instruction) is ast.Expr and hasattr(self._instruction.value, "func"):
            self._operates_on = get_function_name_strings(self._instruction.value)
        elif type(self._instruction) is ast.Return and type(self._instruction.value) is ast.Call:
            self._operates_on = get_function_name_strings(self._instruction.value)
        elif type(self._instruction) is ast.Raise:
            self._operates_on = [self._instruction.type.func.id]
        elif type(self._instruction) is ast.Pass:
            self._operates_on = ["pass"]
        else:
            self._operates_on = [self._instruction]

    def set_target_state(self, state):
        self._target_state = state
        """if not(type(self._instruction) is str):
            state._previous_edge = self"""
        state._previous_edge = self

    def __repr__(self):
        return "<Edge %s>" % self._instruction
