import random
from collections import defaultdict

from program.program import ProgramGraph
import globs

def run_filter(log_analyzer, dynamic_analyzer, inputs, program, multiple, repeat=5):
    print(program)
    counter = defaultdict(int)
    program = program.to_multiline(globs.synthesizer._entries, counter)
    program.simplify()
    print(program)

    results = []

    # try n times
    for _ in range(repeat):
        # initialize environment with input values
        dynamic_analyzer.reset_env()
        for arg_name, arg_type in inputs.items():
            vals = log_analyzer.get_values_by_type(arg_type)
            vals = list({v:v for v in vals}.keys())
            arg_val = random.choice(vals)
            dynamic_analyzer.push_var(arg_name, arg_val)

        # execute the program with collected traces
        r, score = program.execute(dynamic_analyzer)
        print("****Program returns", r)
        results.append((r, score))

    # decide multiplicity
    all_none = True
    all_singleton = True
    all_multiple = True
    all_empty = True
    scores = []
    for result, score in results:
        if result is not None:
            if result:
                all_empty = False

            all_none = False
            while isinstance(result, list) and len(result) == 1:
                all_multiple = False
                if len(result) == 0:
                    break

                result = result[0]

            if isinstance(result, list) and len(result) > 1:
                all_singleton = False

            scores.append(score)

    # if all_singleton:
    #     print("this program returns a singleton")
    # else:
    #     print("this program does not always return a singleton")
    #     print(results)

    # check methods always fail
    if all_none:
        return 999999.9

    # check multiplicity match
    score_avg = sum(scores) / len(scores)
    if all_singleton and multiple:
        print("expects multiple values, but this program does not match the multiplicity")
        score_avg = score_avg + 5.0

    if all_multiple and not multiple:
        print("expects single value, but this program does not match the multiplicity")
        score_avg = score_avg + 10.0

    # penalty on all empty results
    if all_empty:
        score_avg = score_avg + 5.0

    # check field matches
    # log_analyzer.reset_context()
    # var_to_trans = {}
    # # pg = ProgramGraph()
    # # program.to_program_graph(pg, var_to_trans)
    # match, _ = program.check_fields(log_analyzer, var_to_trans)
    # print(match)
    # if not match:
    #     print("this program contains fields not in the response")
    #     score_avg = score_avg - 10.0

    return score_avg