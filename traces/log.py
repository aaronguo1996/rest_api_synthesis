class Parameter:
    def __init__(self, arg_name, value):
        self.arg_name = arg_name
        self.value = value

    def __str__(self):
        return self.__dict__

class ResponseParameter(Parameter):
    def __init__(self, arg_name, path, value):
        super().__init__(arg_name, value)
        self.path = path

    def flatten(self):
        if isinstance(self.value, dict):
            results = []
            for k, v in self.value.items():
                p = ResponseParameter(k, self.path + [k], v)
                results += p.flatten()
            return results
        else:
            return [self]

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.path == other.path and
                self.value == other.value)

class RequestParameter(Parameter):
    def __init__(self, arg_name, func_name, value):
        super().__init__(arg_name, value)
        self.func_name = func_name

    def __eq__(self, other): 
        if not isinstance(other, ResponseParameter):
            # don't attempt to compare against unrelated types
            return NotImplemented

        return (self.arg_name == other.arg_name and
                self.func_name == other.func_name and
                self.value == other.value)

class LogEntry:
    def __init__(self, endpoint, method, parameters, responses):
        self.endpoint = endpoint
        self.method = method
        self.parameters = parameters
        self.responses = responses