class DSU:
    def __init__(self):
        self.parents = {}
        self.sizes = {}
        self.nexts = {}

    def find(self, x):
        if self.parents[x] != x:
            self.parents[x] = self.find(self.parents[x])
            
        return self.parents[x]

    def union(self, x, y):
        if x not in self.parents:
            self.parents[x] = x
            self.sizes[x] = 1
            self.nexts[x] = x

        if y not in self.parents:
            self.parents[y] = y
            self.sizes[y] = 1
            self.nexts[y] = y

        xr, yr = self.find(x), self.find(y)
        if self.sizes[xr] < self.sizes[yr]:
            self.parents[yr] = xr
            # swap the next pointer of xr and yr
            self.nexts[yr], self.nexts[xr] = self.nexts[xr], self.nexts[yr]
            self.sizes[xr] += self.sizes[yr]
        elif (self.sizes[yr] < self.sizes[xr] or 
            xr != yr): # if they have the same size but are different nodes
            self.parents[xr] = yr
            # swap the next point of xr and yr
            self.nexts[xr], self.nexts[yr] = self.nexts[yr], self.nexts[xr]
            self.sizes[yr] += self.sizes[xr]

    def groups(self):
        groups = []
        for x in self.parents:
            if self.parents[x] == x:
                groups.append(self.getGroup(x))

        return groups

    def getGroup(self, x):
        '''
            get all the elements in the same group as @x@
        '''
        result = [x]
        cur = x
        nxt = self.nexts[x]
        while x != nxt:
            result.append(nxt)
            cur, nxt = nxt, self.nexts[cur]

        return result

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
        value = str(param.value)
        
        # skip empty values, they are meaningless
        if not value:
            return

        if value not in self.value_to_param:
            self.value_to_param[value] = param

        root = self.value_to_param[value]
        self.dsu.union(root, param)

    def analysis_result(self):
        return self.dsu.groups()