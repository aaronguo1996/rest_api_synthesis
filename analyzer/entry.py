from traces import typeChecker
from openapi import defs
import re

class Parameter:
    def __init__(self, method, arg_name, func_name, is_required, typ, value=None):
        self.method = method
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value
        self.type = typ
        self.is_required = is_required

    def __str__(self):
        return self.__dict__

    def __repr__(self):
        return self.__str__()

class ErrorResponse:
    def __init__(self, msg):
        self._error_msg = msg

    def __str__(self):
        return f"error: {self._error_msg}"

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        if isinstance(other, ErrorResponse):
            return NotImplemented

        return self._error_msg == other._error_msg

class ResponseParameter(Parameter):
    def __init__(self, method, arg_name, func_name, path, typ, value):
        super().__init__(method, arg_name, func_name, True, typ, value)
        self.path = path

    def _assign_type(self, value):
        if isinstance(value, dict):
            type_dict = value.copy()
            for k in type_dict:
                type_dict[k] = self._assign_type(type_dict[k])
        elif isinstance(value, list):
            item_types = [self._assign_type(v) for v in value]
            item_type = {}
            for t in item_types:
                item_type.update(t)

            type_dict = {
                "type": "array",
                "items": item_type,
            }
        else:
            type_dict = {
                "type": "string",
            }
        
        return type_dict

    def flatten(self, path_to_defs, skip_fields):
        results = []

        if self.arg_name in skip_fields:
            return results

        # if self.func_name == "/conversations.info":
        #     print(f"conversations.info has arg {self.arg_name} of response type", self.type)

        if isinstance(self.value, dict):
            if (defs.DOC_OK not in self.value and 
                (not self.type or self.type.name[:11] == "unknown_obj")): # when we don't know its type
                self.type = typeChecker.Type.infer_type_for(
                    path_to_defs, skip_fields, self.value)

                # if self.func_name == "/conversations.info":
                #     print(f"conversations.info has arg {self.arg_name} of response type", self.type)
                #     print("type schema is", self.type.schema)

            if not self.type and defs.DOC_OK not in self.value:
                # print(f"assigning type for {self.value}")
                assigned_type = self._assign_type(self.value)
                self.type = typeChecker.Type("unknown_obj", assigned_type)

            for k, v in self.value.items():
                if k in skip_fields:
                    continue

                if self.type and self.type.schema and self.type.get_field_schema(k):
                    typ = typeChecker.Type(
                        self.type.name + "." + k, 
                        self.type.get_field_schema(k),
                        self.type)
                else:
                    typ = None

                p = ResponseParameter(
                    self.method, k, self.func_name,
                    self.path + [k], typ, v)
                results += p.flatten(path_to_defs, skip_fields)
        elif isinstance(self.value, list):
            #TODO: infer type for each element in the array
            # if we are able to match an object type against it, we get rid of the index from the path
            # if we cannot match an object against it, leave the index as the arg name
            for i in range(len(self.value)):
                item_type = typeChecker.Type.infer_type_for(
                    path_to_defs, skip_fields, self.value[i])

                if not item_type:
                    self.type = typeChecker.Type("unknown_list", self._assign_type(self.value))
                    item_type = typeChecker.Type("unknown_obj", self.type.schema.get("items"))
                
                p = ResponseParameter(
                    self.method, defs.INDEX_ANY, self.func_name,
                    self.path + [defs.INDEX_ANY], 
                    item_type, self.value[i])

                results += p.flatten(path_to_defs, skip_fields)
        else:
            return [self]

        return results

    def path_to_str(self, rep):
        return 0, rep
        # ind = [p for p in self.path if p == defs.INDEX_ANY]
        # cnt = len(ind)
        # return cnt, "[" * cnt + rep + "]" * cnt

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.method.upper() == other.method.upper() and 
                self.path == other.path)

    def __str__(self):
        return self.arg_name + '_' + self.func_name + '_' + self.method.upper() + '_' + '.'.join(self.path)

    def __hash__(self):
        return hash((self.arg_name, self.func_name, self.method.upper(), tuple(self.path)))

class RequestParameter(Parameter):
    def __init__(self, method, arg_name, func_name, is_required, typ, value):
        super().__init__(method, arg_name, func_name, is_required, typ, value)

    def __eq__(self, other): 
        if not isinstance(other, RequestParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.method.upper() == other.method.upper() and
                self.func_name == other.func_name)

    def __str__(self):
        return self.func_name + ':' + self.arg_name + ':' + self.method.upper()

    def __hash__(self):
        return hash((self.arg_name, self.method.upper(), self.func_name))

class TraceEntry:
    def __init__(self, endpoint, method, parameters, response):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.response = response

    def __str__(self):
        param_strs = map(str, self.parameters)
        return (self.method.upper() + " " + self.endpoint + "\n" +
                ",".join(param_strs) + "\n" + str(self.response))