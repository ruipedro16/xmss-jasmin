#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json
import platform
import psutil
import re
import subprocess
import statistics

import argparse
import pandas as pd


def get_system_info():
    cpufreq = psutil.cpu_freq()
    cpuname = ""
    info = {}

    command = "cat /proc/cpuinfo"
    all_info = subprocess.check_output(command, shell=True).decode().strip()
    for line in all_info.split("\n"):
        if "model name" in line:
            cpuname = re.sub(".*model name.*:", "", line, 1)

    info["platform"] = platform.system()
    info["platform-release"] = platform.release()
    info["platform-version"] = platform.version()
    info["architecture"] = platform.machine()
    info["processor"] = cpuname
    info["min_requency"] = f"{cpufreq.min:.2f}Mhz"
    info["max_requency"] = f"{cpufreq.max:.2f}Mhz"
    info["system_info"]["frequency_used"] = "3.6Mhz"
    info["physical cores"] = psutil.cpu_count(logical=False)
    info["total cores"] = psutil.cpu_count(logical=True)
    info["ram"] = f"{round(psutil.virtual_memory().total/1000000000, 2)} GB"

    return info


def main():

    parser = argparse.ArgumentParser()

    parser.add_argument(
        "-in",
        "--input_file",
        required=True,
        help="Input file path",
        type=str,
    )

    # if -out is not set, we print to stdout
    parser.add_argument(
        "-out",
        "--output_file",
        required=False,
        help="Output file path",
        type=str,
    )

    args = parser.parse_args()

    results = {}
    results["system_info"] = get_system_info()

    df = pd.read_csv(args.input_file)

    algorithms = df["Function"].unique()

    for alg in algorithms:
        filtered_df = df[df["Function"] == alg]
        measurements_ref = filtered_df["Reference"].to_list()
        measurements_jasmin = filtered_df["Jasmin"].to_list()

        assert len(measurements_ref) == len(measurements_jasmin)
        assert len(measurements_ref) > 0

        if len(measurements_jasmin) > 1:
            median_ref = statistics.median(measurements_ref)
            median_jasmin = statistics.median(measurements_jasmin)
        else:
            median_ref = measurements_ref[0]
            median_jasmin = median_jasmin[0]

        results[alg] = {"ref": median_ref, "jasmin": median_jasmin}

    if out := args.output_file:
        with open(out, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=4)
    else:
        print(json.dumps(results, indent=4))


if __name__ == "__main__":
    main()
