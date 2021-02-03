from collections import defaultdict

def group_params(params):
    result = defaultdict(int)
    for p in params:
        result[str(p.type)] += 1

    return result