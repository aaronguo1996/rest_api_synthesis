def get_representative(group):
    rep = ""
    rep_type = None
    for param in group:
        path_str = str(param.type)
        if ("unknown_obj" not in path_str and param.type and
            (not rep or len(rep) >= len(path_str))):
            if len(rep) == len(path_str) and path_str >= rep:
                continue

            rep = path_str
            rep_type = param.type

    return rep, rep_type