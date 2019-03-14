import pandas as ps
import sys
import os

TRIVIAL_RTL = 32

def main(results_dir, tex_csv_dir, translations_file, virtual_timeout):
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
            status = get_status(err_content, virtual_timeout)
            is_ok = get_status_ok(status)
            seconds = get_seconds(err_content)
            if is_ok:
                result = get_result(log_content)
            else:
                result = "no result"
            results[config + "/" + smt_file] = status + "," + result + "," + seconds
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
    df["seconds"] = df.err_log.apply(lambda x: x.split(",")[2])
    validate_stat_res(df)
    validate_consistency(df)
    validate_no_sat_except_qf_and_cond_inv(df)
    df["proved"] = df.result.apply(lambda x: "yes" if (x == "unsat") else "no")
    
    
    cond_grouped = df.groupby(["ic_name", "direction", "encoding", "cond_inv"], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})

    yes_filter = df.loc[df["proved"] == "yes"]
    yes_grouped = yes_filter.groupby(["ic_name", "direction", "encoding", "cond_inv"], as_index=False)
    time_agg = yes_grouped.agg({'seconds': 'min'})
    
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


    only_combined = df.loc[df["encoding"] == "combined"].copy()
    red_configs = andy_configs(only_combined)
    print("panda red configs", red_configs)
    red_encodings = andy_encodings(enc_agg)
    print("panda red encs", red_encodings)

    print(keep_encodings(enc_agg, ["combined", "partial", "full"]))
    print(keep_configs(only_combined, ["z3_default", "cvc4_tplanes", "vampire" ]))


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
    time_agg.to_csv("tmp/tmp12.csv")

    tex_stuff(ic_agg, direction_agg, cond_agg, config_cond_agg, tex_csv_dir, translations_file)

def tex_stuff(ic_agg, direction_agg, cond_agg, config_cond_agg, tex_csv_dir, translations_file):
    gen_IC_status_tables(direction_agg, tex_csv_dir)
    enc_conds = gen_encoding_cond_tables(cond_agg, tex_csv_dir)
    gen_rtl_yes_ics(cond_agg, tex_csv_dir, translations_file)
    gen_enc_conf(config_cond_agg, translations_file, tex_csv_dir)
    #gen_numbers(ic_agg, direction_agg, enc_conds, tex_csv_dir)
        


def gen_enc_conf(config_cond_agg, translations_file, tex_csv_dir):
    ic_names = config_cond_agg["ic_name"].tolist()
    ics = gen_ics_from_translations_file(ic_names, translations_file)
    ics = clean_ics(ics)
    tmp = config_cond_agg.copy()
    tmp["ic"] = tmp["ic_name"].apply(get_ic_from_name(ics))
    tmp = tmp.loc[(tmp["ic"] != "true") | (tmp["direction"] == "ltr")].copy()

    g = tmp.groupby(["encoding", "config", "ic_name", "direction"], as_index = False)
    c = g.agg({'proved': agg_yes})
    pivot = c.pivot_table(index=["encoding"], columns = "config", values = "proved", aggfunc = countyes)

    #totals for encodings
    g = c.groupby(["encoding", "ic_name", "direction"], as_index = False)
    a = g.agg({'proved': agg_yes})
    g = a.groupby(["encoding"], as_index = True)
    b = g.agg({'proved': countyes})
    s = b["proved"]
    g = a.groupby(["ic_name", "direction"], as_index = False)
    a = g.agg({'proved': agg_yes})
    s["total"] = len(a.loc[a["proved"] == "yes"].index)
    pivot["total"] = s
    
    #totals for configs
    g = c.groupby(["config", "ic_name", "direction"], as_index = False)
    a = g.agg({'proved': agg_yes})
    a.to_csv("~/tmp.csv")
    g = a.groupby(["config"], as_index = True)
    b = g.agg({'proved': countyes})
    s = b["proved"]
    g = a.groupby(["ic_name", "direction"], as_index = False)
    a = g.agg({'proved': agg_yes})
    s["total"] = len(a.loc[a["proved"] == "yes"].index)
    pivot.loc["total"] = s
    pivot.to_csv(tex_csv_dir + "/enc_con.csv")

def gen_numbers(ic_agg, direction_agg, enc_conds, tex_csv_dir):
    ics_proved = ic_agg.loc[ic_agg["proved"] == "yes"].copy()
    num_proved = len(ics_proved.index)
    sides_proved = direction_agg.loc[direction_agg["proved"] == "yes"].copy()
    ltr_proved = sides_proved.loc[sides_proved["direction"] == "ltr"]
    rtl_proved = sides_proved.loc[sides_proved["direction"] == "rtl"]
    num_ltr_proved = len(ltr_proved.index)
    num_rtl_proved = len(rtl_proved.index)


    with open(tex_csv_dir + "/total_proved.tex", "w") as myfile:
        myfile.write(str(num_proved))
    with open(tex_csv_dir + "/ltr_proved.tex", "w") as myfile:
        myfile.write(str(num_ltr_proved))
    with open(tex_csv_dir + "/rtl_proved.tex", "w") as myfile:
        myfile.write(str(num_rtl_proved))
    

def gen_rtl_yes_ics(cond_agg, tex_csv_dir, translations_file):
    ic_names = cond_agg["ic_name"].tolist()
    ics = gen_ics_from_translations_file(ic_names, translations_file)
    ics = clean_ics(ics)
    proved = cond_agg.loc[cond_agg["direction"] == "rtl"].copy()
    proved["ic"] = proved["ic_name"].apply(get_ic_from_name(ics))
    tmp = proved.loc[proved["ic"] == "true"]
    tmp = tmp.loc[tmp["proved"] == "no"]
    assert(len(tmp.index) == 0)
    proved = proved.loc[proved["proved"] == "yes"].copy()
    proved.to_csv(tex_csv_dir + "/" + "ics_rtl.csv")

def gen_ics_from_translations_file(ic_names, translation_file):
    result = {}
    with open(translation_file, "r") as myfile:
        lines = myfile.readlines()
    for line in lines:
        name = line.split(",")[0]
        ic = line.split(",")[2]
        result[name] = ic
    return result

def clean_ics(ics):
    return {name[len("int_check_"):] : ics[name] for name in ics}

def get_ic_from_name(ics):
    return lambda name : ics[name]

def concat_special(row):
    direction = row["direction"]
    cond = row["cond_inv"]
    if direction == "rtl":
        return direction
    else:
        assert(direction == "ltr")
        return direction + "_" + cond

def cond_inv_yes(row):
    if row["ltr_inv_a"] == "yes" or row["ltr_inv_g"] == "yes" or row["ltr_inv_r"] == "yes":
        return "yes"
    else:
        return "no"

def ltr_yes(row):
    if row["ltr_inv"] == "yes" or row["ltr_no_inv"] == "yes":
        return "yes"
    else:
        return "no"

def ltr_only(row):
    if row.ltr == "yes" and row.rtl == "no":
        return "yes"
    else:
        return "no"

def rtl_only(row):
    if row.rtl == "yes" and row.ltr == "no":
        return "yes"
    else:
        return "no"

def fully_proved(row):
    if row.rtl == "yes" and row.ltr == "yes":
        return "yes"
    else:
        return "no"

def nothing_proved(row):
    if row.rtl == "no" and row.ltr == "no":
        return "yes"
    else:
        return "no"

def inv_only(row):
    if row["ltr_inv"] == "yes" and row["ltr_no_inv"] == "no":
        return "yes"
    else:
        return "no"

def no_inv_only(row):
    if row["ltr_inv"] == "no" and row["ltr_no_inv"] == "yes":
        return "yes"
    else:
        return "no"

def gen_encoding_cond_tables(cond_agg, tex_csv_dir):
    cond_agg["direction_cond"] = cond_agg.apply(concat_special, axis=1)
    pivot = cond_agg.pivot_table(index = ["encoding", "ic_name"], columns = "direction_cond", values = "proved", aggfunc = lambda x : " ".join(x)).reset_index()
    pivot["ltr_inv"] = pivot.apply(cond_inv_yes, axis=1)
    pivot["ltr"] = pivot.apply(ltr_yes, axis=1)
    pivot["ltr_inv_only"] = pivot.apply(inv_only, axis=1)
    pivot["ltr_no_inv_only"] = pivot.apply(no_inv_only, axis=1)
    pivot["ltr_only"] = pivot.apply(ltr_only, axis=1)
    pivot["rtl_only"] = pivot.apply(rtl_only, axis=1)
    pivot["fully_proved"] = pivot.apply(fully_proved, axis=1)
    pivot["nothing_proved"] = pivot.apply(nothing_proved, axis=1)
    
    over_encs_gb = pivot.groupby(["ic_name"])
    over_encs = over_encs_gb.agg(agg_yes)
    over_encs = over_encs.drop("encoding", axis=1)
    

    group_by = pivot.groupby(["encoding"]) 
    agg = group_by.agg(countyes)
    #do another pivot for total according to direction and cond.
    g = cond_agg.groupby(["ic_name", "direction_cond"], as_index =False)
    a = g.agg({'proved': agg_yes})
    ap = a.pivot_table(index = ["ic_name"], columns = "direction_cond", values = "proved", aggfunc = lambda x: " ".join(x)).reset_index()
    ap["ltr_inv"] = ap.apply(cond_inv_yes, axis=1)
    ap["ltr"] = ap.apply(ltr_yes, axis=1)
    ap["ltr_inv_only"] = ap.apply(inv_only, axis=1)
    ap["ltr_no_inv_only"] = ap.apply(no_inv_only, axis=1)
    ap["ltr_only"] = ap.apply(ltr_only, axis=1)
    ap["rtl_only"] = ap.apply(rtl_only, axis=1)
    ap["fully_proved"] = ap.apply(fully_proved, axis=1)
    ap["nothing_proved"] = ap.apply(nothing_proved, axis=1)
    ap = ap.set_index("ic_name")
    s = ap.apply(countyes)
    s.name = "total"

    agg.loc["total"] = s
    agg = agg.drop("ic_name", axis=1)
    agg = agg.astype(int)
    agg["rtl_non_trivial"] = agg["rtl"].apply(lambda x : int(x) - TRIVIAL_RTL)
    agg["rtl_complex"] = agg.apply(lambda row : str(row["rtl"]) + "~(" + str(row["rtl_non_trivial"])  + ")", axis=1 )
    
    agg = agg.rename(under_to_middle ,axis='columns')
    #output is what is going to the csv. agg is what is returned, with all info.
    output = agg.copy() 
    output.to_csv(tex_csv_dir + "/" + "cond_detailed.csv")
    output = output.drop("rtl", axis=1)
    output = output.drop("rtl-non-trivial", axis=1)
    output = output.drop("ltr-inv-a", axis=1)
    output = output.drop("ltr-inv-g", axis=1)
    output = output.drop("ltr-inv-r", axis=1)
    titles = ['fully-proved', 'nothing-proved', 'rtl-only', 'ltr-only', 'ltr-inv', 'ltr-no-inv']
    output = output.reindex(columns = titles)
    output.to_csv(tex_csv_dir + "/" + "cond.csv")
    return agg.copy()

def under_to_middle(s):
    return s.replace("_", "-")

def countyes(ser):
    l = ser.tolist()
    return len([a for a in l if a == "yes"])

def gen_IC_status_tables(direction_agg, tex_csv_dir):
    pivot = direction_agg.pivot_table(index = "ic_name", columns = "direction", values = "proved", aggfunc = lambda x: ' '.join(x))
#    pivot.columns = pivot.columns.droplevel()
    pivot = pivot.reset_index()
    pivot.columns=pivot.columns.tolist()
    pivot["relation"] = pivot["ic_name"].apply(lambda x: x.split('_')[0])
    pivot["operation"] = pivot["ic_name"].apply(lambda x: x.split('_')[1])
    pivot["family"] = pivot["relation"].apply(get_family)
    pivot["direction_proved"] = pivot.apply(what_proved, axis=1)
    
    summary = pivot.pivot_table(index = "operation", columns = "relation", values = "direction_proved", aggfunc = lambda x: ' '.join(x))
    columnsTitles = ['eq', 'ne', 'bvult', 'bvugt', 'bvule', 'bvuge', 'bvslt', 'bvsgt', 'bvsle', 'bvsge']

    summary = summary.reindex(columns=columnsTitles)
    summary.to_csv(tex_csv_dir + "/" + "summary" + ".csv")
    
#    tables = {}
#    families = set(pivot["family"].tolist())
#    for family in families:
#        filtered = pivot.loc[pivot["family"] == family]
#        tables[family] = filtered.pivot_table(index = "operation", columns = "relation", values = "direction_proved", aggfunc = lambda x: ' '.join(x))
#        tables[family] = tables[family].reset_index()
#        tables[family].columns=tables[family].columns.tolist()
#        tables[family].to_csv(tex_csv_dir + "/" + family + ".csv")

def what_proved(row):
    if row["ltr"] == "yes" and row["rtl"] == "yes":
        return "\\both"
    if row.ltr == "yes" and row.rtl == "no":
        return "\\ltr"
    if row.ltr == "no" and row.rtl == "yes":
        return "\\rtl"
    if row.ltr == "no" and row.rtl == "no":
        return "\\none"

def get_family(s):
    if s in ["eq", "ne"]:
        return "equality"
    if s in ["bvult", "bvugt"]:
        return "unsigned_strong"
    if s in ["bvule", "bvuge"]:
        return "unsigned_weak"
    if s in ["bvslt", "bvsgt"]:
        return "signed_strong"
    if s in ["bvsle", "bvsge"]:
        return "signed_weak"
    assert(False)

def keep_configs(df, configs_to_keep):
    configs = set(df["config"].tolist())
    assert(set(configs_to_keep).issubset(configs))
    encodings = set(df["encoding"].tolist())
    assert len(encodings) == 1 and "combined" in encodings
    df = df.drop(columns = ["encoding"])
    cond_grouped = df.groupby(["ic_name", "direction", "config", ], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})
    df["to_keep"] = df.config.apply(lambda x: x in configs_to_keep)
    dff = df.loc[df["to_keep"] == True].copy()
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
    dff = df.loc[df["to_drop"] == False].copy()
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def drop_encodings(df, encodings_to_drop):
    df["to_drop"] = df.encoding.apply(lambda x: x in encodings_to_drop)
    dff = df.loc[df["to_drop"] == False].copy()
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index).copy()


def keep_encodings(df, encodings_to_keep):
    df["to_keep"] = df.encoding.apply(lambda x: x in encodings_to_keep)
    dff = df.loc[df["to_keep"] == True].copy()
    dff_grouped = dff.groupby(["ic_name", "direction"], as_index=False)
    dff_agg = dff_grouped.agg({'proved' : agg_yes})
    return len(dff_agg.loc[dff_agg["proved"] == "yes"].index)


def andy_encodings(df):
    redundent_encodings = set([])
    encodings = set(df['encoding'].tolist())
    d = {}
    for encoding in encodings:
        df_e = df.loc[df.encoding == encoding].copy()
        df_e_yes = df_e.loc[df_e.proved == "yes"].copy()
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
                    print(e1, e2)
                    redundent_encodings.add(e1)
    return redundent_encodings

def andy_configs(df):
    encodings = set(df["encoding"].tolist())
    assert len(encodings) == 1 and "combined" in encodings
    df = df.drop(columns = ["encoding"])
    cond_grouped = df.groupby(["ic_name", "direction", "config", ], as_index=False)
    cond_agg = cond_grouped.agg({'proved' : agg_yes})

    redundent_configs = set([])
    configs = set(df['config'].tolist())
    d = {}
    for config in configs:
        df_e = df.loc[df.config == config].copy()
        df_e_yes = df_e.loc[df_e.proved == "yes"].copy()
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
    return redundent_configs

def validate_no_sat_except_qf_and_cond_inv(df):
    no_qf = df.loc[df.encoding != "qf"].copy()
    no_qf = no_qf.loc[no_qf.encoding != "qf_ind"].copy()
    no_qf = no_qf.loc[(no_qf["cond_inv"] != "inv_a") & (no_qf["cond_inv"] != "inv_g") & (no_qf["cond_inv"] != "inv_r") ]
    sat = no_qf.loc[no_qf.result == "sat"].copy()
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
    if row.status == "ok" and row.result not in ["sat", "unsat", "unknown", "no result"]:
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

def get_seconds(err_content):
    lines = err_content.splitlines()
    prefix = "[runlim] time:"
    time_lines = [line for line in lines if line.startswith(prefix)]
    if len(time_lines) == 0:
        return "no_time"
    elif len(time_lines) > 1:
        assert(False)
    else:
        assert(len(time_lines) == 1)
        time_line = time_lines[0]
        time = time_line[len(prefix):].split(".")[0].strip()
        return time

# no virtual timeout - put -1
def get_status(err_content, virtual_to):
    lines = err_content.splitlines()
    prefix = "[runlim] status:"
    status_lines = [line for line in lines if line.startswith(prefix)]
    if len(status_lines) == 0:
        return "no status"
    elif len(status_lines) > 1:
        assert(False)
    else:
        assert(len(status_lines) == 1)
        status_line = status_lines[0]
        status = status_line[len(prefix):].strip()
        #vampire errors
        if "User error" in err_content:
            return "error"
        else:
            if virtual_to == -1:
                return status
            else:
                time = get_seconds(err_content)
                if time == "no_time" or int(time) > virtual_to:
                    return "out of time"
                else:
                    return status

def get_status_ok(status):
    return status == "ok"

def get_result(log_content):
    lines = log_content.splitlines()
    bad_prefix = "c"
    good_lines = [l for l in lines if not l.startswith(bad_prefix)]
    if len(good_lines) == 0 or "Memory limit exceeded" in "\n".join(good_lines): 
        return "no result"
    elif len(good_lines) > 1:
        assert(False)
    else:
        good_line = good_lines[0]
        return good_line


if __name__ == "__main__":
    if len(sys.argv) < 4:
        print('arg1: cluster results dir\narg2: tex-csv dir\narg3: translations file\noptional arg4: virtual timeout in seconds (-1 if none)')
        exit(1)
    results_dir = sys.argv[1]
    tex_csv_dir = sys.argv[2]
    translation_file = sys.argv[3]
    if len(sys.argv) == 5:
        virtual_timeout = int(sys.argv[4])
    else:
        virtual_timeout = -1
    
    main(results_dir, tex_csv_dir, translation_file, virtual_timeout)
