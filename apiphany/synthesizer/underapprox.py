
class Approximation:
    def __init__(self, net):
        self._net = net

    def approx_reachability(self, inputs, outputs):
        forward_reachables = self._compute_reachability(
            self._net.post, inputs, set(), set())
        backward_reachables = self._compute_reachability(
            self._net.pre, outputs, set(), set())
        return forward_reachables.intersection(backward_reachables)

    def _compute_reachability(self, direction, inputs, visited, reachables):
        if not inputs:
            return reachables

        output_places = []
        for pl in inputs:
            if pl in visited:
                continue

            visited.add(pl)
            post_trans = direction(pl)
            reachables = reachables.union(set(post_trans))
            for trans in post_trans:
                output_places += direction(trans)

        return self._compute_reachability(
            direction, output_places, visited, reachables)
