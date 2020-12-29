NUM_PARAMS_EACH = 20

class DSU:
    def __init__(self):
        self.parents = {}
        self.sizes = {}

    def find(self, x):
        if x in self.parents and self.parents[x] != x:
            self.parents[x] = self.find(self.parents[x])
            return self.parents[x]

    def union(self, x, y):
        if x not in self.parents:
            self.parents[x] = x
            self.sizes[x] = 1

        if y not in self.parents:
            self.parents[y] = y
            self.sizes[y] = 1

        xr, yr = self.find(x), self.find(y)
        if self.sizes[xr] < self.sizes[yr]:
            self.parents[yr] = xr
            self.sizes[xr] += self.sizes[yr]
        elif (self.sizes[yr] < self.sizes[xr] or 
            xr != yr): # if they have the same size but are different nodes
            self.parents[xr] = yr
            self.sizes[yr] += self.sizes[xr]

class LogAnalyzer:
    def __init__(self):
        self.value_to_param = {}
        self.dsu = DSU()

    def analyze(self, entries):
        '''
            Match the value of each request argument or response parameter
            in a log entry and union the common ones
        '''
        for entry in entries:
            for p in entry.parameters:
                self.insert(p)
            for r in entry.responses:
                self.insert(r)

    def insert(self, param):
        value = param.value
        if value not in self.value_to_param:
            self.value_to_param[value] = param

        root = self.value_to_param[value]
        self.dsu.union(root, param)