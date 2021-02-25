from collections import defaultdict
from copy import copy
import time

STATS_SEARCH = "search"
STATS_ENCODE = "encode"
STATS_GRAPH = "graph"

class TimeStats:
    _timing = defaultdict(float)

    def __init__(self, key):
        self._key = key

    def __call__(self, func):
        def wrapper(*args, **kwargs):
            start = time.time()
            result = func(*args, **kwargs)
            end = time.time()
            Stats.add_entry(self._key, end - start)
            return result

        return wrapper

    @staticmethod
    def add_entry(key, value):
        Stats._timing[key] += value

    @staticmethod
    def reset():
        Stats._timing = defaultdict(float)