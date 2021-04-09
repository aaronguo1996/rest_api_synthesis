
class Approximation:
    def __init__(self, net):
        self._net = net

    def approx_reachability(self, inputs, visited, reachables):
        if not inputs:
            return reachables

        output_places = []
        for pl in inputs:
            if pl in visited:
                continue

            visited.add(pl)
            post_trans = self._net.post(pl)
            reachables = reachables.union(set(post_trans))
            for trans in post_trans:
                output_places += self._net.post(trans)

        return self.approx_reachability(output_places, visited, reachables)
