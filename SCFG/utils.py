"""
SCFG utility functions.
"""
import ast

def get_function_name_strings(obj):
    """
    For a given ast object, get the fully qualified function names of all function calls
    found in the object.
    """
    chain = list(ast.walk(obj))
    all_calls = list(filter(lambda item: type(item) is ast.Call, chain))
    ##print(all_calls)
    full_names = {}
    for call in all_calls:
        # construct the full function name for this call
        current_item = call
        full_names[call] = []
        while not (type(current_item) is str):
            if type(current_item) is ast.Call:
                current_item = current_item.func
            elif type(current_item) is ast.Attribute:
                full_names[call].append(current_item.attr)
                current_item = current_item.value
            elif type(current_item) is ast.Name:
                full_names[call].append(current_item.id)
                current_item = current_item.id
            elif type(current_item) is ast.Str:
                # full_names[call].append(current_item.s)
                current_item = current_item.s
            elif type(current_item) is ast.Subscript:
                current_item = current_item.value
    return list(map(lambda item: ".".join(reversed(item)), full_names.values()))


def get_reversed_string_list(obj, omit_subscripts=False):
    """
    For a given ast object, find the reversed list representation of the names inside it.
    Eg, A.b() will give [b, A]
    """
    if type(obj) is ast.Name:
        return [obj.id]
    elif type(obj) is ast.Attribute:
        return [obj.attr] + get_reversed_string_list(obj.value, omit_subscripts=omit_subscripts)
    elif type(obj) is ast.Subscript:
        if omit_subscripts:
            return get_reversed_string_list(obj.value)
        else:
            if type(obj.slice.value) is ast.Str:
                return ["[\"%s\"]" % obj.slice.value.s] + get_reversed_string_list(obj.value,
                                                                                   omit_subscripts=omit_subscripts)
            elif type(obj.slice.value) is ast.Num:
                return ["[%i]" % obj.slice.value.n] + get_reversed_string_list(obj.value,
                                                                               omit_subscripts=omit_subscripts)
            elif type(obj.slice.value) is ast.Name:
                return ["[%s]" % obj.slice.value.id] + get_reversed_string_list(obj.value,
                                                                                omit_subscripts=omit_subscripts)
    elif type(obj) is ast.Call:
        return get_function_name_strings(obj)
    elif type(obj) is ast.Str:
        return [obj.s]


def get_attr_name_string(obj, omit_subscripts=False):
    """
    For an ast object
    """
    attr_string = ""
    if type(obj) in [ast.Load, ast.Index]:
        return None
    else:
        result = get_reversed_string_list(obj, omit_subscripts=omit_subscripts)[::-1]
        for (n, part) in enumerate(result):
            if "." in part and len(result) > 1:
                # all cases in the will be covered individually by traversal
                return None
            else:
                if part[0] != "[":
                    attr_string += "%s%s" % ("." if n != 0 else "", part)
                else:
                    attr_string += part
        return attr_string