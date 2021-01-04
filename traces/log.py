class Parameter:
    def __init__(self, arg_name, func_name, value):
        self.arg_name = arg_name
        self.func_name = func_name
        self.value = value

    def __str__(self):
        return self.__dict__

    def __repr__(self):
        return self.__str__()

class ResponseParameter(Parameter):
    def __init__(self, arg_name, func_name, path, value):
        super().__init__(arg_name, func_name, value)
        self.path = path

    def flatten(self):
        results = []
        if isinstance(self.value, dict):
            for k, v in self.value.items():
                p = ResponseParameter(k, self.func_name, self.path + [k], v)
                results += p.flatten()
        elif isinstance(self.value, list):
            #TODO: infer type for each element in the array
            # if we are able to match an object type against it, we get rid of the index from the path
            # if we cannot match an object against it, leave the index as the arg name
            for i in range(len(self.value)):
                p = ResponseParameter(str(i), self.func_name, self.path + ["["+ str(i) +"]"], self.value[i])
                results += p.flatten()
        else:
            return [self]

        return results

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.path == other.path)

    def __str__(self):
        return '.'.join(self.path)

    def __hash__(self):
        return hash((self.arg_name, str(self.path)))

class RequestParameter(Parameter):
    def __init__(self, arg_name, func_name, value):
        super().__init__(arg_name, func_name, value)

    def __eq__(self, other): 
        if not isinstance(other, RequestParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name)

    def __str__(self):
        return self.func_name + ':' + self.arg_name

    def __hash__(self):
        return hash((self.arg_name, self.func_name))

class LogEntry:
    def __init__(self, endpoint, method, parameters, responses):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.responses = responses

    def __str__(self):
        param_strs = map(str, self.parameters)
        resp_strs = map(str, self.responses)
        return (self.method.upper() + " " + self.endpoint + "\n" +
                ",".join(param_strs) + "\n" +
                ",".join(resp_strs))