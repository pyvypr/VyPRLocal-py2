"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""

This module contains logic for construction of a specialised control flow graph.

"""

import ast

from VyPR.monitor_synthesis import formula_tree
from VyPR.QueryBuilding import *
from VyPR.SCFG.components import *
from VyPR.SCFG.utils import *

vertices = []

"""
AST decision functions.
"""


def ast_is_try(ast_obj):
    return type(ast_obj) is ast.TryExcept


def ast_is_assign(ast_obj):
    return type(ast_obj) is ast.Assign or type(ast_obj) is ast.AugAssign


def ast_is_call(ast_obj):
    return type(ast_obj) is ast.Call


def ast_is_expr(ast_obj):
    return type(ast_obj) is ast.Expr


def ast_is_pass(ast_obj):
    return type(ast_obj) is ast.Pass


def ast_is_return(ast_obj):
    return type(ast_obj) is ast.Return


def ast_is_raise(ast_obj):
    return type(ast_obj) is ast.Raise


def ast_is_if(ast_obj):
    return type(ast_obj) is ast.If


def ast_is_for(ast_obj):
    return type(ast_obj) is ast.For


def ast_is_while(ast_obj):
    return type(ast_obj) is ast.While


def ast_is_continue(ast_obj):
    return type(ast_obj) is ast.Continue


def ast_is_break(ast_obj):
    return type(ast_obj) is ast.Break


"""
End of AST type checking funcitons.
"""


class CFG(object):
    """
    This class represents a symbolic control flow graph.
    """

    def __init__(self, reference_variables=[]):
        self.vertices = []
        self.edges = []
        empty_vertex = CFGVertex()
        self.vertices.append(empty_vertex)
        self.starting_vertices = empty_vertex
        self.return_statements = []
        self.branch_initial_statements = []
        self.reference_variables = reference_variables
        # we have a stack of continue vertices so we can construct edges going from continue vertices
        # to the end of loops once they've been computed
        self.continue_vertex_stack = []

    def process_block(self, block, starting_vertices=None, condition=[], closest_loop=None):
        """
        Given a block, a set of starting vertices and to put on the first edge,
        construct the section of the control flow graph corresponding to this block.
        """
        # make a copy of the condition sequence for this branch
        condition = [c for c in condition]
        current_vertices = starting_vertices if not (starting_vertices is None) else [self.starting_vertices]
        path_length = 0

        for (n, entry) in enumerate(block):
            # print("processing block")
            if ast_is_assign(entry) or (ast_is_expr(entry) and ast_is_call(entry.value)):
                path_length += 1
                # print("processing assignment")

                # for each vertex in current_vertices, add an edge
                new_edges = []
                for vertex in current_vertices:
                    entry._parent_body = block
                    # print("constructing new edge")
                    new_edge = CFGEdge(condition, entry)
                    new_edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)

                # create a new vertex for the state created here
                new_vertex = CFGVertex(entry, path_length=path_length, reference_variables=self.reference_variables)

                self.vertices.append(new_vertex)
                self.edges += new_edges

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # update current vertices
                current_vertices = [new_vertex]

            elif ast_is_pass(entry):
                path_length += 1
                entry._parent_body = block

                # for each vertex in current_vertices, add an edge
                new_edges = []
                for vertex in current_vertices:
                    entry._parent_body = block
                    # print("constructing new edge")
                    new_edge = CFGEdge(condition, entry)
                    new_edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)

                # create a new vertex for the state created here
                new_vertex = CFGVertex(entry, path_length=path_length)

                self.vertices.append(new_vertex)
                self.edges += new_edges

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # update current vertices
                current_vertices = [new_vertex]

            elif ast_is_return(entry):
                path_length += 1

                new_edges = []
                for vertex in current_vertices:
                    entry._parent_body = block
                    new_edge = CFGEdge(condition, entry)
                    new_edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)

                new_vertex = CFGVertex(entry, path_length=path_length)

                self.vertices.append(new_vertex)
                self.edges += new_edges

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # update current vertices
                current_vertices = [new_vertex]

                self.return_statements.append(new_vertex)

            elif ast_is_raise(entry):
                path_length += 1

                new_edges = []
                for vertex in current_vertices:
                    entry._parent_body = block
                    new_edge = CFGEdge(condition, entry)
                    new_edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)

                new_vertex = CFGVertex(entry, path_length=path_length)

                self.vertices.append(new_vertex)
                self.edges += new_edges

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # update current vertices
                current_vertices = [new_vertex]

            elif ast_is_break(entry):
                # we assume that we're inside a loop
                # this instruction doesn't generate a vertex - rather it generates an edge
                # leading to the ending vertex given by closest_loop
                path_length += 1

                loop_ending_edge = CFGEdge("break", "break")
                self.edges.append(loop_ending_edge)
                loop_ending_edge.set_target_state(closest_loop)
                for vertex in current_vertices:
                    vertex.add_outgoing_edge(loop_ending_edge)

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # set the current_vertices to empty so no constructs can make an edge
                # from the preceding statement
                current_vertices = []

            elif ast_is_continue(entry):
                # we assume that we're inside a loop
                # this instruction generates a continue vertex
                # which is picked up by the post-loop processing so an edge can be added from this vertex
                # to the last vertex of the loop body
                path_length += 1

                new_edges = []
                for vertex in current_vertices:
                    entry._parent_body = block
                    new_edge = CFGEdge(condition, entry)
                    new_edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)

                new_vertex = CFGVertex(entry)

                self.vertices.append(new_vertex)
                self.edges += new_edges

                # direct all new edges to this new vertex
                for edge in new_edges:
                    edge.set_target_state(new_vertex)

                # add this continue vertex to the continue vertex stack
                self.continue_vertex_stack.append(new_vertex)

                # continue ends control-flow on this branch, so we can return to processing the block above
                return []

            elif ast_is_if(entry):

                entry._parent_body = block
                path_length += 1

                # if this conditional isn't the last element in its block, we need to place a post-conditional
                # path recording instrument after it
                if entry != entry._parent_body[-1]:
                    self.branch_initial_statements.append(["post-conditional", entry])

                # insert intermediate control flow vertex at the beginning of the block
                empty_conditional_vertex = CFGVertex(structure_obj=entry)
                empty_conditional_vertex._name_changed = ['conditional']
                self.vertices.append(empty_conditional_vertex)

                # connect empty_conditional_vertex to the graph constructed so far
                for vertex in current_vertices:
                    new_edge = CFGEdge("conditional", "control-flow")
                    self.edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)
                    new_edge.set_target_state(empty_conditional_vertex)
                current_vertices = [empty_conditional_vertex]

                # process the conditional block
                current_conditional = [entry]
                final_else_is_present = False
                final_conditional_vertices = []
                branch_number = 0

                # process the main body, and then iterate downwards
                final_vertices = self.process_block(
                    current_conditional[0].body,
                    current_vertices,
                    [current_conditional[0].test],
                    closest_loop
                )
                # add to the list of final vertices that need to be connected to the post-conditional vertex
                final_conditional_vertices += final_vertices
                # add the branching statement
                self.branch_initial_statements.append(
                    ["conditional", current_conditional[0].body[0], branch_number]
                )
                branch_number += 1

                # we now repeat the same, but iterating through the conditional structure
                while type(current_conditional[0]) is ast.If:
                    current_conditional = current_conditional[0].orelse
                    if len(current_conditional) == 1:

                        # there is just another conditional block, so process it as if it were a branch
                        if type(current_conditional[0]) is ast.If:
                            # pairs.append(
                            #     (current_condition_set + [current_conditional[0].test], current_conditional[0].body))
                            # current_condition_set.append(formula_tree.lnot(current_conditional[0].test))
                            final_vertices = self.process_block(
                                current_conditional[0].body,
                                current_vertices,
                                [current_conditional[0].test],
                                closest_loop
                            )
                            # add to the list of final vertices that need to be connected to the post-conditional vertex
                            final_conditional_vertices += final_vertices
                            # add the branching statement
                            self.branch_initial_statements.append(
                                ["conditional", current_conditional[0].body[0], branch_number]
                            )
                            branch_number += 1

                        else:
                            # the else block contains an instruction that isn't a conditional
                            # pairs.append((current_condition_set, current_conditional))
                            final_vertices = self.process_block(
                                current_conditional,
                                current_vertices,
                                ["else"],
                                closest_loop
                            )
                            # we reached an else block
                            final_else_is_present = True
                            # add to the list of final vertices that need to be connected to the post-conditional vertex
                            final_conditional_vertices += final_vertices
                            # add the branching statement
                            self.branch_initial_statements.append(
                                ["conditional", current_conditional[0], branch_number]
                            )
                            branch_number += 1

                    elif len(current_conditional) > 1:
                        # there are multiple blocks inside the orelse, so we can't treat this like another branch
                        final_vertices = self.process_block(
                            current_conditional,
                            current_vertices,
                            ["else"],
                            closest_loop
                        )
                        final_conditional_vertices += final_vertices
                        self.branch_initial_statements.append(
                            ["conditional", current_conditional[0], branch_number]
                        )
                        # we reached an else block
                        final_else_is_present = True
                    else:
                        # nowhere else to go in the traversal
                        break

                # we include the vertex before the conditional, only if there was no else
                if not (final_else_is_present):
                    # we add a branching statement - the branch number is just the number of pairs we found
                    self.branch_initial_statements.append(["conditional-no-else", entry, branch_number])
                    current_vertices = final_conditional_vertices + current_vertices
                else:
                    current_vertices = final_conditional_vertices

                # filter out vertices that were returns or raises
                # here we have to check for the previous edge existing, in case the program starts with a conditional
                current_vertices = list(filter(
                    lambda vertex: vertex._previous_edge is None or not (
                            type(vertex._previous_edge._instruction) in [ast.Return, ast.Raise]),
                    current_vertices
                ))

                # add an empty "control flow" vertex after the conditional
                # to avoid transition duplication along the edges leaving
                # the conditional
                if len(current_vertices) > 0:
                    empty_vertex = CFGVertex()
                    empty_vertex._name_changed = ['post-conditional']
                    # at the moment, used for grammar construction from the scfg
                    empty_conditional_vertex.post_conditional_vertex = empty_vertex
                    self.vertices.append(empty_vertex)
                    for vertex in current_vertices:
                        # an empty edge
                        new_edge = CFGEdge("post-condition", "control-flow")
                        self.edges.append(new_edge)
                        new_edge.set_target_state(empty_vertex)
                        vertex.add_outgoing_edge(new_edge)

                    current_vertices = [empty_vertex]
                else:
                    empty_conditional_vertex.post_conditional_vertex = None

                condition.append("skip-conditional")

                # reset path length for instructions after conditional
                path_length = 0

            elif ast_is_try(entry):
                entry._parent_body = block
                path_length += 1
                # print("processing try-except")

                if entry != entry._parent_body[-1]:
                    self.branch_initial_statements.append(["post-try-catch", entry])

                # insert intermediate control flow vertex at the beginning of the block
                empty_conditional_vertex = CFGVertex()
                empty_conditional_vertex._name_changed = ['try-catch']
                self.vertices.append(empty_conditional_vertex)
                for vertex in current_vertices:
                    new_edge = CFGEdge("try-catch", "control-flow")
                    self.edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)
                    new_edge.set_target_state(empty_conditional_vertex)
                current_vertices = [empty_conditional_vertex]

                blocks = []
                self.branch_initial_statements.append(["try-catch", entry.body[0], "try-catch-main"])

                # print("except handling blocks are:")

                for except_handler in entry.handlers:
                    self.branch_initial_statements.append(["try-catch", except_handler.body[0], "try-catch-handler"])
                    # print(except_handler.body)
                    blocks.append(except_handler.body)

                # print("final list of except blocks is")
                # print(blocks)

                # print("processing blocks")

                # first process entry.body
                final_try_catch_vertices = []

                final_vertices = self.process_block(
                    entry.body,
                    current_vertices,
                    ['try-catch-main'],
                    closest_loop
                )
                final_try_catch_vertices += final_vertices

                # now process the except handlers - eventually with some identifier for each branch

                for block_item in blocks:
                    # print(block_item)
                    # print("="*10)
                    final_vertices = self.process_block(
                        block_item,
                        current_vertices,
                        ['try-catch-handler'],
                        closest_loop
                    )
                    final_try_catch_vertices += final_vertices
                # print("="*10)

                current_vertices = final_try_catch_vertices

                # print(current_vertices)

                # filter out vertices that were returns or raises
                # this should be applied to the other cases as well - needs testing
                current_vertices = list(filter(
                    lambda vertex: vertex._previous_edge is None or not (
                            type(vertex._previous_edge._instruction) in [ast.Return, ast.Raise]),
                    current_vertices
                ))

                # print("processing try-except end statements")
                # print(current_vertices)

                if len(current_vertices) > 0:
                    empty_vertex = CFGVertex()
                    empty_vertex._name_changed = ['post-try-catch']
                    empty_conditional_vertex.post_try_catch_vertex = empty_vertex
                    self.vertices.append(empty_vertex)
                    for vertex in current_vertices:
                        # an empty edge
                        new_edge = CFGEdge("post-try-catch", "control-flow")
                        self.edges.append(new_edge)
                        new_edge.set_target_state(empty_vertex)
                        vertex.add_outgoing_edge(new_edge)

                    current_vertices = [empty_vertex]
                else:
                    empty_conditional_vertex.post_try_catch_vertex = None

                condition.append("skip-try-catch")
                path_length = 0

            elif ast_is_for(entry):
                entry._parent_body = block
                path_length += 1

                # this will eventually be modified to include the loop variable as the state changed

                empty_pre_loop_vertex = CFGVertex(structure_obj=entry)
                empty_pre_loop_vertex._name_changed = ['loop']
                empty_post_loop_vertex = CFGVertex()
                empty_post_loop_vertex._name_changed = ['post-loop']
                self.vertices.append(empty_pre_loop_vertex)
                self.vertices.append(empty_post_loop_vertex)

                # link current_vertices to the pre-loop vertex
                for vertex in current_vertices:
                    new_edge = CFGEdge(entry.iter, "loop")
                    self.edges.append(new_edge)
                    vertex.add_outgoing_edge(new_edge)
                    new_edge.set_target_state(empty_pre_loop_vertex)

                current_vertices = [empty_pre_loop_vertex]

                # process loop body
                # first, determine the additional input variables that this loop induces
                loop_variable = entry.target
                if type(loop_variable) is ast.Name:
                    additional_input_variables = [loop_variable.id]
                elif type(loop_variable) is ast.Tuple:
                    additional_input_variables = list(map(lambda item: item.id, loop_variable.elts))
                final_vertices = self.process_block(
                    entry.body,
                    current_vertices,
                    ['enter-loop'],
                    empty_post_loop_vertex
                )

                # for a for loop, we add a path recording instrument at the beginning of the loop body
                # and after the loop body
                self.branch_initial_statements.append(["loop", entry.body[0], "enter-loop", entry, "end-loop"])

                # add 2 edges from the final_vertex - one going back to the pre-loop vertex
                # with the positive condition, and one going to the post loop vertex.

                for final_vertex in final_vertices:
                    # there will probably only ever be one final vertex, but we register a branching vertex
                    # self.branching_vertices.append(final_vertex)
                    for base_vertex in current_vertices:
                        new_positive_edge = CFGEdge('loop-jump', 'loop-jump')
                        self.edges.append(new_positive_edge)
                        final_vertex.add_outgoing_edge(new_positive_edge)
                        new_positive_edge.set_target_state(base_vertex)

                        new_post_edge = CFGEdge("post-loop", "post-loop")
                        self.edges.append(new_post_edge)
                        final_vertex.add_outgoing_edge(new_post_edge)
                        new_post_edge.set_target_state(empty_post_loop_vertex)

                # process all of the continue vertices on the stack
                for continue_vertex in self.continue_vertex_stack:
                    new_edge = CFGEdge("post-loop", "post-loop")
                    self.edges.append(new_edge)
                    continue_vertex.add_outgoing_edge(new_edge)
                    new_edge.set_target_state(empty_pre_loop_vertex)
                    self.continue_vertex_stack.remove(continue_vertex)

                skip_edge = CFGEdge(formula_tree.lnot(entry.iter), "loop-skip")
                empty_pre_loop_vertex.add_outgoing_edge(skip_edge)
                # skip_edge.set_target_state(final_vertices[0])
                skip_edge.set_target_state(empty_post_loop_vertex)

                current_vertices = [empty_post_loop_vertex]
                # current_vertices = final_vertices

                condition.append("skip-for-loop")

                # reset path length for instructions after loop
                path_length = 0

            elif ast_is_while(entry):
                # needs work - but while loops haven't been a thing we've needed to handle so far
                # need to add code to deal with branching vertices
                path_length += 1

                # this should be updated at some point to include empty pre and post-loop vertices like in the for
                # loop clause above

                final_vertices = self.process_block(entry.body, current_vertices, ['while'], closest_loop)

                for final_vertex in final_vertices:
                    for base_vertex in current_vertices:
                        new_positive_edge = CFGEdge('for', 'loop-jump')
                        self.edges.append(new_positive_edge)
                        final_vertex.add_outgoing_edge(new_positive_edge)
                        new_positive_edge.set_target_state(base_vertex)

                current_vertices = final_vertices

        return current_vertices

    def derive_grammar(self):
        """
        Derive a dictionary mapping vertices to lists of symbol lists.
        The symbols are either edges (terminal symbols) or vertices (non-terminal symbols).
        """
        # print("constructing context free grammar from scfg")
        final_map = {}
        for vertex in self.vertices:
            # print(vertex)
            # check for the type of vertex
            if len(vertex.edges) == 0:

                # control flow can end at this vertex - the rule for it should just generate the empty string
                final_map[vertex] = [[None]]

            elif not (vertex._name_changed in [["conditional"], ["loop"], ["try-catch"], ["post-conditional"],
                                               ["post-loop"], ["post-try-catch"]]):

                # a normal vertex, but we care about what it leads to since this determines the "special" structure of rules we generate

                # print(vertex._name_changed)
                # we handle conditionals and try-catches together at the moment, because they have similar structure
                if not (vertex.edges[0]._target_state._name_changed in [["conditional"], ["try-catch"]]):

                    # check which vertices this leads to

                    if vertex.edges[0]._target_state._name_changed in [["post-conditional"], ["post-try-catch"]]:
                        final_map[vertex] = [[vertex.edges[0]]]
                    elif any(map(lambda edge: edge._target_state._name_changed == ["post-loop"], vertex.edges)):
                        # we have to deal with some branching
                        reloop_edge = \
                            list(filter(lambda edge: edge._target_state._name_changed == ["loop"], vertex.edges))[0]
                        loop_skip_edge = \
                            list(filter(lambda edge: edge._target_state._name_changed != ["loop"], vertex.edges))[0]
                        final_map[vertex] = [[reloop_edge, reloop_edge._target_state], [loop_skip_edge]]
                    elif vertex.edges[0]._target_state._name_changed == ["loop"]:
                        post_loop_vertex = list(filter(
                            lambda edge: edge._target_state._name_changed == ["post-loop"],
                            vertex.edges[0]._target_state.edges
                        ))[0]._target_state
                        final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state, post_loop_vertex]]
                    else:
                        # normal vertex that isn't followed by any special structure
                        if vertex.edges[0]._target_state._name_changed in [["post-conditional"], ["post-loop"],
                                                                           ["post-try-catch"]]:
                            final_map[vertex] = [[vertex.edges[0]]]
                        else:
                            final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state]]

                elif vertex.edges[0]._target_state._name_changed == ["conditional"]:

                    # get the edge that leads to the end of the conditional
                    post_conditional_vertex = vertex.edges[0]._target_state.post_conditional_vertex
                    if post_conditional_vertex:
                        final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state, post_conditional_vertex]]
                    else:
                        final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state]]

                elif vertex.edges[0]._target_state._name_changed == ["try-catch"]:

                    # get the edge that leads to the end of the try-catch
                    post_try_catch_vertex = vertex.edges[0]._target_state.post_try_catch_vertex
                    if post_try_catch_vertex:
                        final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state, post_try_catch_vertex]]
                    else:
                        final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state]]

            elif vertex._name_changed == ["loop"]:

                # find the loop-skip edge
                loop_skip_edge = \
                    list(filter(lambda edge: edge._target_state._name_changed == ["post-loop"], vertex.edges))[0]
                final_map[vertex] = [[loop_skip_edge]]
                loop_entry_edge = \
                    list(filter(lambda edge: edge._target_state._name_changed != ["post-loop"], vertex.edges))[
                        0]
                final_map[vertex].append([loop_entry_edge, loop_entry_edge._target_state])


            elif vertex._name_changed in [["conditional"], ["try-catch"]]:

                final_map[vertex] = []
                for edge in vertex.edges:
                    # we check whether we're looking at an edge that leads straight past the conditional
                    # and directly to the post-conditional vertex
                    if edge._target_state._name_changed == ["post-conditional"]:
                        final_map[vertex].append([edge])
                    else:
                        final_map[vertex].append([edge, edge._target_state])

            elif vertex._name_changed == ["post-conditional"]:

                # check whether we're inside a loop
                if vertex.edges[0]._target_state._name_changed == ["loop"]:
                    # if we're inside a loop, then we need to include the post-loop edge
                    final_map[vertex] = [
                        [vertex.edges[0], vertex.edges[0]._target_state],
                        [vertex.edges[1]]
                    ]
                elif vertex.edges[0]._target_state._name_changed == ["post-conditional"]:
                    final_map[vertex] = [[vertex.edges[0]]]
                else:
                    final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state]]

            else:

                if vertex.edges[0]._target_state._name_changed in [["post-conditional"], ["post-loop"],
                                                                   ["post-try-catch"]]:
                    final_map[vertex] = [[vertex.edges[0]]]
                else:
                    final_map[vertex] = [[vertex.edges[0], vertex.edges[0]._target_state]]

        # print(final_map[vertex])

        return final_map

    def next_calls(self, vertex, function, calls=[], marked_vertices=[]):
        """
        Given a point (vertex or edge), find the set of next edges that model calls to function.
        """
        if not (vertex in marked_vertices):
            marked_vertices.append(vertex)
            edges = vertex.edges
            for edge in edges:
                if ((type(edge._instruction) is ast.Expr
                     and hasattr(edge._instruction.value, "func")
                     and function in get_function_name_strings(edge._instruction.value))
                        or
                        (type(edge._instruction) is ast.Assign
                         and type(edge._instruction.value) is ast.Call and function in get_function_name_strings(
                                    edge._instruction.value))):
                    calls.append(edge)
                else:
                    # this edge is not what we're looking for
                    # so traverse this branch further
                    self.next_calls(edge._target_state, function, calls, marked_vertices)
        else:
            pass


def expression_as_string(expression):
    if type(expression) is ast.Num:
        return str(expression.n)
    else:
        return str(expression)


def instruction_to_string(instruction):
    if type(instruction) is ast.Assign:
        return "%s = %s" % (get_attr_name_string(instruction.targets[0]), expression_as_string(instruction.value))
    elif type(instruction) is ast.Expr:
        return "%s()" % get_function_name_strings(instruction.value)
