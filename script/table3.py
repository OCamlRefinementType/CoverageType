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

def show_source(source, name):
    return f"\\textsf{{{name}}}{tab[source]}"

def show_is_rec(is_rec, branches):
    if is_rec:
        return branches + "†"
    else:
        return branches

def append_line (res, x):
    return res + " & " + x

benchmarks = [
    "SizedList",
    "SortedList",
    "UniqueList",
    "SizedTree",
    "CompleteTree",
    "RedBlackTree",
    "SizedBST",
    "BatchedQueue",
    "BankersQueue",
    "Stream",
    "SizedHeap",
    "LeftistHeap",
    "SizedSet",
    "UnbalanceSet"]

midrule_list = [ "UniqueList" , "SizedBST" , "BankersQueue" , "Stream" , "LeftistHeap"]


def show_data(data):
    for bench in benchmarks:
        j = data[bench]
        res = show_source(j["source"], bench)
        res = append_line (res, "${}$".format(j["branchs"]))
        if j["if_rec"]:
            res = append_line (res, "$\\checkmark$")
        else:
            res = append_line (res, " ")
        res = append_line (res, "${}$".format(j["lvar"]))
        res = append_line (res, "${}$".format(j["mp"]))
        res = append_line (res, "${}$".format(j["num_query"]))
        res = append_line (res, "$({}, {})$".format(j["max_forall"], j["max_exists"]))
        res = append_line (res, "${:.2f}({:.2f})$".format(1000*j["total_time"], 1000*j["avg_time"]))
        res = res + " \\\\"
        print(res)
        if bench in midrule_list:
            print("\midrule")

if __name__ == '__main__':
    if_verbose = None
    try:
        if sys.argv[1] == "verbose":
            if_verbose = True
    except:
        if_verbose = False
    table = {}
    for key in tab:
        p = "data/PLDI23/" + key
        for name in os.listdir(p):
            path = p + "/" + name
            print(path)
            run_bench.run(path, if_verbose)
            try:
                with open("/tmp/coverage_type_stat.json", 'r') as file:
                    j = json.load(file)
                    if len(j) == 1:
                        j[0]["source"] = key
                    else:
                        exit(1)
                    table[name] = j[0]
            except Exception as e:
                print(f"An unexpected error occurred: {e}")
                exit(1)
    data = {}
    for bench in benchmarks:
        data[bench] = table[bench + ".ml"]
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
