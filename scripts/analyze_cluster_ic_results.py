import pandas as ps
import sys
import os

def main(results_dir, output_file):
    results = {}
    results_dirs = [d for d in os.listdir(results_dir)]
    for d in results_dirs:
        config = d
        directory = results_dir + "/" + d
        err_files = [f for f in os.listdir(directory) if f.endswith(".err") and not f.startswith(".")]
        for err_file in err_files:
            log_file = err_file.replace(".smt2.err", ".smt2.log")
            smt_file = err_file.replace(".smt2.err", ".smt2")
            with open(directory + "/" + err_file, "r") as myfile:
                err_content = myfile.read()
            with open(directory + "/" + log_file, "r") as myfile:
                log_content = myfile.read()
            status = get_status(err_content)
            is_ok = get_status_ok(status)
            if is_ok:
                result = get_result(log_content)
            else:
                result = "no result"
            results[config + "/" + smt_file] = status + "," + result
    df = ps.DataFrame(list(results.items()))
    df.index = df.index.rename("index")
    df.columns = [ 'path', 'err_log']
    df["config"] = df.path.apply(lambda x : x.split("/")[0])
    df["filename"] = df.path.apply(lambda x : x.split("/")[1])
    df["encoding"] = df.filename.apply(lambda x : x.split("-")[0])
    df["filename_clean"] = df.filename.apply(lambda x : x.split("-")[1].split(".")[0])
    df["relation"] = df.filename_clean.apply(lambda x: x.split("_")[2])
    df["operator"] = df.filename_clean.apply(lambda x: x.split("_")[3])
    df["ic_name"] = df.filename_clean.apply(lambda x: "_".join(x.split("_")[2:4]))
    df["direction"] = df.filename_clean.apply(lambda x: x.split("_")[4])
    df["cond_inv"] = df.filename_clean.apply(cond_inv_info)
    df["status"] = df.err_log.apply(lambda x: x.split(",")[0])
    df["result"] = df.err_log.apply(lambda x: x.split(",")[1])
    validate_stat_res(df)
    validate_consistency(df)
    #validate_no_sat_except_qf(df)
    #TODO uncomment...
    df["proved"] = df.result.apply(lambda x: "yes" if (x == "unsat") else "no")

    
    cond_grouped = df.groupby(["ic_name", "direction", "encoding", "cond_inv"], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})
    
    enc_grouped = cond_agg.groupby(["ic_name", "direction", "encoding"], as_index = False)
    enc_agg = enc_grouped.agg({'proved' : agg_yes})
    
    direction_grouped = enc_agg.groupby(["ic_name", "direction"], as_index = False)
    direction_agg = direction_grouped.agg({'proved' : agg_yes})
    
    ic_grouped = direction_agg.groupby(["ic_name"], as_index=False)
    ic_agg = ic_grouped.agg({'proved' : agg_both_yes})
    
    config_cond_grouped = df.groupby(["encoding", "config", "ic_name", "direction", "cond_inv"], as_index = False)
    config_cond_agg = config_cond_grouped.agg({'proved' : agg_yes})

    config_ic_grouped = config_cond_agg.groupby(["encoding", "config", "ic_name", "direction"])
    config_ic_agg = config_ic_grouped.agg({'proved': agg_yes})

    config_grouped = config_ic_agg.groupby(["encoding", "config"])
    config_agg = config_grouped.agg({'proved': agg_count_yes})

    enc_alone_grouped = config_ic_agg.groupby(["encoding", "ic_name", "direction"])
    enc_alone_agg = enc_alone_grouped.agg({'proved':agg_yes})

    enc_sum_grouped = enc_alone_agg.groupby(["encoding"])
    enc_sum_agg = enc_sum_grouped.agg({'proved':agg_count_yes})

    conf_alone_grouped = config_ic_agg.groupby(["config", "ic_name", "direction"])
    conf_alone_agg = conf_alone_grouped.agg({'proved':agg_yes})

    conf_sum_grouped = conf_alone_agg.groupby(["config"])
    conf_sum_agg = conf_sum_grouped.agg({'proved':agg_count_yes})

    encodings_to_drop = ["rec_ind", "full_ind", "qf_ind", "partial_ind"]
    proved = drop_encodings(enc_agg, encodings_to_drop)

    encodings_to_keep = ["full", "partial"]
    proved = keep_encodings(enc_agg, encodings_to_keep)

    only_partial = df.loc[df["encoding"] == "partial"]
    andy_configs(only_partial)
    proved = drop_configs(only_partial, ["cvc4_tplanes", "cvc4_fmf", "cvc4_cbqi", "cvc4_default"])
    proved = keep_configs(only_partial, ["cvc4_default", "cvc4_tplanes_fmf"])
    print("panda", proved)


    df.to_csv("tmp/tmp0.csv")
    cond_agg.to_csv("tmp/tmp1.csv")
    enc_agg.to_csv("tmp/tmp2.csv")
    direction_agg.to_csv("tmp/tmp3.csv")
    ic_agg.to_csv("tmp/tmp4.csv")
    config_cond_agg.to_csv("tmp/tmp5.csv")
    config_ic_agg.to_csv("tmp/tmp6.csv")
    config_agg.to_csv("tmp/tmp7.csv")
    enc_alone_agg.to_csv("tmp/tmp8.csv")
    enc_sum_agg.to_csv("tmp/tmp9.csv")
    conf_alone_agg.to_csv("tmp/tmp10.csv")
    conf_sum_agg.to_csv("tmp/tmp11.csv")



def keep_configs(df, configs_to_keep):
    configs = set(df["config"].tolist())
    assert(set(configs_to_keep).issubset(configs))
    print(configs_to_keep)
    encodings = set(df["encoding"].tolist())
    assert len(encodings) == 1 and "partial" in encodings
    df = df.drop(columns = ["encoding"])
    cond_grouped = df.groupby(["ic_name", "direction", "config", ], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})
    df["to_keep"] = df.config.apply(lambda x: x in configs_to_keep)
    dff = df.loc[df["to_keep"] == True]
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def drop_configs(df, configs_to_drop):
    configs = set(df["config"].tolist())
    assert(set(configs_to_drop).issubset(configs))
    encodings = set(df["encoding"].tolist())
    assert len(encodings) == 1 and "partial" in encodings
    df = df.drop(columns = ["encoding"])
    cond_grouped = df.groupby(["ic_name", "direction", "config", ], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})
    df["to_drop"] = df.config.apply(lambda x: x in configs_to_drop)
    dff = df.loc[df["to_drop"] == False]
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def drop_encodings(df, encodings_to_drop):
    df["to_drop"] = df.encoding.apply(lambda x: x in encodings_to_drop)
    dff = df.loc[df["to_drop"] == False]
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def keep_encodings(df, encodings_to_keep):
    df["to_keep"] = df.encoding.apply(lambda x: x in encodings_to_keep)
    dff = df.loc[df["to_keep"] == True]
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def andy_encodings(df):
    redundent_encodings = set([])
    encodings = set(df['encoding'].tolist())
    d = {}
    for encoding in encodings:
        print("panda", encoding)
        df_e = df.loc[df.encoding == encoding]
        df_e_yes = df_e.loc[df_e.proved == "yes"]
        df_e_yes["full_name"] = df_e_yes.apply(lambda row: row['ic_name'] + "_" + row['direction'], axis=1)
        l = df_e_yes["full_name"].tolist()
        s = set(l)
        d[encoding] = s

    for e1 in encodings:
        for e2 in encodings:
            if e1 == e2:
                continue
            else:
                if d[e1].issubset(d[e2]):
                    redundent_encodings.add(e1)

def andy_configs(df):
    encodings = set(df["encoding"].tolist())
    assert len(encodings) == 1 and "partial" in encodings
    df = df.drop(columns = ["encoding"])
    cond_grouped = df.groupby(["ic_name", "direction", "config", ], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})

    redundent_configs = set([])
    configs = set(df['config'].tolist())
    d = {}
    for config in configs:
        print("panda", config)
        df_e = df.loc[df.config == config]
        df_e_yes = df_e.loc[df_e.proved == "yes"]
        df_e_yes["full_name"] = df_e_yes.apply(lambda row: row['ic_name'] + "_" + row['direction'], axis=1)
        l = df_e_yes["full_name"].tolist()
        s = set(l)
        d[config] = s

    for e1 in configs:
        for e2 in configs:
            if e1 == e2:
                continue
            else:
                if d[e1] == d[e2]:
                    print("panda same:", e1, e2)
                if d[e1].issubset(d[e2]):
                    redundent_configs.add(e1)
    print("panda", redundent_configs)

def validate_no_sat_except_qf(df):
    no_qf = df.loc[df.encoding != "qf"]
    no_qf = no_qf.loc[no_qf.encoding != "qf_ind"]
    sat = no_qf.loc[no_qf.result == "sat"]
    if len(sat.index) != 0:
        print("\n".join(sat.path.tolist()))
        assert(False)


def agg_count_yes(values):
    l = [a for a in values.tolist() if a == "yes"]
    return len(l)

def print_groups(gs):
    for name_of_the_group, group in gs:
        print (name_of_the_group)
        print (group)
        print("")

def agg_both_yes(values):
    l = values.tolist()
    if (len(l) != 2):
        assert(False)
    assert(l[0] in ["yes", "no"] and l[1] in ["yes", "no"])
    if l[0] == "yes" and l[1] == "yes":
        return "yes"
    else:
        return "no"

def agg_yes(values):
    if "yes" in values.tolist():
        return "yes"
    else:
        return "no"

def validate_consistency(df):
    pivot = df.pivot_table(index='filename', columns='config', values='result', aggfunc=lambda x: ' '.join(x))
    pivot["consistent"] = pivot.apply(consistent, axis=1)

def consistent(row):
    l = row.tolist()
    result = ( not ("sat" in l and "unsat" in l))
    assert(result)
    return result

def validate_stat_res_row(row):
    if row.status == "ok" and row.result not in ["sat", "unsat", "unknown"]:
        return False
    if row.status != "ok" and row.result in ["sat", "unsat", "unknown"]:
        return False
    if row.status == "out of time" and row.result != "no result":
        return False
    if row.status == "out of memory" and row.result != "no result":
        return False
    return True

def validate_stat_res(df):
    bla = df.apply(validate_stat_res_row, axis = 1)
    blist = bla.tolist()
    assert((False not in blist))

def cond_inv_info(s):
    if s.endswith("_rtl"):
        result = "NA"
    else:
        if "_ltr_" not in s:
            assert(False)
        result = "_".join(s.split("_")[5:])
        if result not in ["no_inv", "inv_a", "inv_g", "inv_r"]:
            return result
    return result

def get_status(err_content):
    lines = err_content.splitlines()
    prefix = "[runlim] status:"
    status_lines = [line for line in lines if line.startswith(prefix)]
    assert(len(status_lines) == 1)
    status_line = status_lines[0]
    status = status_line[len(prefix):].strip()
    return status

def get_status_ok(status):
    return status == "ok"

def get_result(log_content):
    lines = log_content.splitlines()
    bad_prefix = "c"
    good_lines = [l for l in lines if not l.startswith(bad_prefix)]
    if len(good_lines) != 1:
        assert(False)
    good_line = good_lines[0]
    return good_line


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print('arg1: cluster results dir\narg2: output file\n')
        exit(1)
    results_dir = sys.argv[1]
    output_file = sys.argv[2]
    main(results_dir, output_file)
