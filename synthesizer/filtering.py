import random

from program.program import ProgramGraph

def run_filter(log_analyzer, dynamic_analyzer, inputs, program, multiple, repeat=5):
    print(program.pretty())
    results = []

    # try n times
    for _ in range(repeat):
        # initialize environment with input values
        dynamic_analyzer.reset_env()
        for arg_name, arg_type in inputs.items():
            # vals = log_analyzer.get_values_by_type(arg_type)
            # print(vals)
            # arg_val = random.choice(vals)
            arg_val = "general"
            # print("choose channel name", arg_val)
            dynamic_analyzer.push_var(arg_name, arg_val)

        # execute the program with collected traces
        r, score = program.execute(dynamic_analyzer)
        results.append((r, score))

    # decide multiplicity
    all_none = True
    all_singleton = True
    scores = []
    for result, score in results:
        if result is not None:
            all_none = False
            while isinstance(result, list) and len(result) == 1:
                if len(result) == 0:
                    break

                result = result[0]

            if isinstance(result, list) and len(result) > 1:
                all_singleton = False

            scores.append(score)

    if all_singleton:
        print("this program returns a singleton")
    else:
        print("this program does not always return a singleton")
        print(results)

    # check methods always fail
    if all_none:
        return -100.0

    # check multiplicity match
    score_avg = sum(scores) / len(scores)
    if all_singleton and multiple:
        print("expects multiple values, but this program does not match the multiplicity")
        score_avg = score_avg - 5.0

    if not all_singleton and not multiple:
        print("expects single value, but this program does not match the multiplicity")
        score_avg = score_avg - 10.0

    # check field matches
    log_analyzer.reset_context()
    var_to_trans = {}
    # pg = ProgramGraph()
    # program.to_program_graph(pg, var_to_trans)
    match, _ = program.check_fields(log_analyzer, var_to_trans)
    print(match)
    if not match:
        print("this program contains fields not in the response")
        score_avg = score_avg - 10.0

    return score_avg