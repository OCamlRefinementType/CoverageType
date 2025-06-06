import sys
import argparse
import os
import json
import run_bench
# from tabulate import tabulate

headers = ["", "#Branch" , "#LocalVar" , "#MP" , "#Query" , "(max. #∀,#∃)" , "total (avg. time)(s)"]

tab = {"elrond": "$^\\diamond$", "quickchick": "*",  "quickcheck": "$^\\circ$", "leonidas": "$^\\star$"}

def parse_stat ():
    line = None
    with open (resfile) as f:
        line = f.readline().split('&')
        line = [elem.replace("\n", "").replace("$", "").replace(" ", "") for elem in line]
    return line

def show_source(name):
    return f"\\textsf{{{name}}}"

def show_is_rec(is_rec, branches):
    if is_rec:
        return branches + "†"
    else:
        return branches

def append_line (res, x):
    return res + " & " + x

func_names =  {
    "Tezos": "tezos_tree_gen",
    "Xen API": "fd_size_gen",
    "Vellvm": "gen_uvalue",
    "Herdtools7": "literal",
    "Zipperposition": "default_fuel",
}

source_file =  {
    "Tezos": "tezos.ml",
    "Xen API": "xen_api.ml",
    "Vellvm": "vellvm.ml",
    "Herdtools7": "herdtools7.ml",
    "Zipperposition": "zipperposition.ml",
}

def show_data(data):
    for bench in source_file:
        j = data[bench]
        res = show_source(bench)
        res = append_line (res, "${}$".format(j["branchs"]))
        if j["if_rec"]:
            res = append_line (res, "$\\checkmark$")
        else:
            res = append_line (res, " ")
        res = append_line (res, "${}$".format(j["lvar"]))
        res = append_line (res, "${}$".format(j["mp"]))
        res = append_line (res, "${}$".format(j["num_query"]))
        res = append_line (res, "$({}, {})$".format(j["max_forall"], j["max_exists"]))
        res = append_line (res, "${:.2f}({:.2f})$".format(j["total_time"], j["avg_time"]))
        res = res + " \\\\"
        print(res)

if __name__ == '__main__':
    if_verbose = None
    try:
        if sys.argv[1] == "verbose":
            if_verbose = True
    except:
        if_verbose = False
    data = {}
    for bench_name in source_file:
        run_bench.run("data/monad/" + source_file[bench_name], if_verbose)
        try:
            with open("/tmp/coverage_type_stat.json", 'r') as file:
                j = json.load(file)
        except Exception as e:
            print(f"An unexpected error occurred: {e}")
            exit(1)
        for stat in j:
            if stat["function_name"] == func_names[bench_name]:
                data[bench_name] = stat
    show_data(data)


    #     source, path, is_rec = iter_benchs.get_info_from_name (benchmark_table, name)
    #     if os.path.exists(resfile):
    #         os.remove(resfile)
    #     run_bench.run(path, if_verbose)
    #     res = parse_stat ()
    #     # print(res)
    #     if res[0] == "false":
    #         print("fail")
    #         exit(1)
    #     else:
    #         res = [name] + res[2:]
    #         data.append((source, is_rec, res))
    # show_data(data)
