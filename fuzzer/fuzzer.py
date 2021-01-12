from fuzzer.error import EndpointNotFoundError

class Fuzzer:
    def __init__(self, openapi_doc):
        self._doc = openapi_doc
        self._paths = openapi_doc["paths"]

    def fuzz_one(self, method, endpoint):
        ep_def = self._paths.get(endpoint)
        if not ep_def:
            raise EndpointNotFoundError(endpoint)
        
        ep_method_def = ep_def.get(method)
        if not ep_method_def:
            raise EndpointNotFoundError(endpoint, method)

        # get parameters
        