import glob
import itertools
import random
import re
import subprocess
import time
from collections import defaultdict
from datetime import datetime
from distutils.file_util import copy_file
from pathlib import Path

import click
import redis
import os
import shutil

from pysat.formula import CNF

HOST = None
PORT = None
REDIS_DECODE_RESPONSES = True
GLOBAL_TIME_FUNCTION_LOG_DICT: [str, float] = defaultdict(int)
CLAUSE_DATABASE: set[tuple[int, ...]] = set()


def timing_decorator(func):
    def wrapper(*args, **kwargs):
        start_time = time.time()
        result = func(*args, **kwargs)
        end_time = time.time()
        elapsed_time = end_time - start_time
        global GLOBAL_TIME_FUNCTION_LOG_DICT
        GLOBAL_TIME_FUNCTION_LOG_DICT[func.__name__] += elapsed_time
        return result

    return wrapper


@timing_decorator
def get_redis_connection():
    return redis.Redis(host=HOST, port=PORT, decode_responses=REDIS_DECODE_RESPONSES)


@timing_decorator
def parse_clauses_with_assertion(line):
    clause_with_zero = line.split()
    assert clause_with_zero[-1] == '0'
    return clause_with_zero[:-1]


@timing_decorator
def get_learnts(last_processed_learnt, buffer_size) -> tuple[int, list[list[int]], list[list[int]]]:
    con = get_redis_connection()
    add_clauses: list[list[int]] = []
    delete_clauses: list[list[int]] = []
    read_learnt: int = 0

    pipe = con.pipeline()
    while True:
        for i in range(buffer_size):
            pipe.get(f'from_minisat:{last_processed_learnt + read_learnt + i}')
        result = pipe.execute()
        for i, clause in enumerate(result):
            if clause:
                add_clauses.append(list(map(int, parse_clauses_with_assertion(clause))))
            else:
                con.close()
                return read_learnt + i, add_clauses, delete_clauses
        read_learnt += buffer_size


@timing_decorator
def find_backdoors(
        search_bin: Path,
        path_tmp_dir: Path,
        combine_path_cnf: Path,
        ea_num_runs: int,
        ea_instance_size: int,
        ea_num_iters: int,
        log_dir: Path):
    # ./target/release/search /Users/aandreev/SAT_SOLVING/distributed_backdoors_search/data/miters/mult/lec_CvK_12.cnf --backdoor-size 10 --num-iters 1000 --num-runs 10  -o backdoors.txt
    log_backdoor = path_tmp_dir / "log_searcher.log"
    backdoor_path = path_tmp_dir / "backdoor.txt"

    if os.path.exists(backdoor_path):
        os.remove(backdoor_path)
        print(f"{backdoor_path} has been removed.")
    else:
        print(f"{backdoor_path} does not exist.")

    ea_seed = random.randint(1, 10000)
    command = f"{search_bin} {combine_path_cnf} --num-runs {ea_num_runs} --seed {ea_seed} --backdoor-size {ea_instance_size} --num-iters {ea_num_iters} -o {backdoor_path} 2>&1 | tee {log_backdoor}"

    process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    stdout, stderr = process.communicate()

    if process.returncode == 0:
        with open(log_dir / "find_backdoors_strout", 'w') as find_backdoors_stdout_file:
            find_backdoors_stdout_file.write(stdout.decode('utf-8'))
            find_backdoors_stdout_file.write("Error\n")
            find_backdoors_stdout_file.write(stderr.decode('utf-8'))
        print("Find backdoors process was successful")
    else:
        raise Exception(f"There are exception during find backdoors files "
                        f"path_tmp_dir = {path_tmp_dir}, "
                        f"combine_path_cnf = {combine_path_cnf} "
                        f"ea_num_runs = {ea_num_runs} "
                        f"ea_seed = {ea_seed} "
                        f"ea_instance_size = {ea_instance_size} "
                        f"ea_num_iters = {ea_num_iters}: \n"
                        f"ERROR: {stderr.decode('utf-8')}"
                        f"STDOUT: {stdout.decode('utf-8')}")
    return backdoor_path


@timing_decorator
def combine(path_cnf, add_clauses, combine_path):
    if not os.path.exists(combine_path):
        print(f"Writing {len(add_clauses)} extracted clauses to new file'{combine_path}'...")
        with open(combine_path, "w") as file:
            with open(path_cnf, 'r') as origin_cnf:
                file.write(origin_cnf.read())
                file.write("\n")
            for clause in add_clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")
    else:
        print(f"Writing {len(add_clauses)} extracted clauses to end file '{combine_path}'...")
        with open(combine_path, "a") as file:
            for clause in add_clauses:
                file.write(" ".join(map(str, clause)) + " 0\n")


@timing_decorator
def derive(derive_bin: Path, combine_path_cnf: Path, backdoors_path: Path, path_tmp_dir: Path, log_dir: Path,
           mini_conf: int):
    derived_clauses = path_tmp_dir / "derived.txt"
    command = f"{derive_bin} {combine_path_cnf} --backdoors @{backdoors_path} --num-conflicts {mini_conf} -o {derived_clauses}"
    process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    if process.returncode == 0:
        with open(log_dir / "minimize_strout", 'w') as minimize_stdout_file:
            minimize_stdout_file.write(stdout.decode('utf-8'))
            minimize_stdout_file.write("Errors\n")
            minimize_stdout_file.write(stderr.decode('utf-8'))
        print("The minimize process was successful")
    else:
        raise Exception(f"There are exception during derive clause "
                        f"combine_path_cnf = {combine_path_cnf}, "
                        f"backdoors_path = {backdoors_path} "
                        f"path_tmp_dir = {path_tmp_dir}: \n"
                        f"ERROR: {stderr.decode('utf-8')}"
                        f"STDOUT: {stdout.decode('utf-8')}")

    return derived_clauses


@timing_decorator
def copy_to(file, to_dir):
    try:
        shutil.copy(file, to_dir)
        print(f"File '{file}' copied to '{to_dir}' successfully.")
    except FileNotFoundError as e:
        print(f"File '{file}' not found.")
        raise e
    except IsADirectoryError as e:
        print(f"'{to_dir}' is not a valid directory.")
        raise e
    except PermissionError as e:
        print(f"You don't have permission to copy to '{to_dir}'.")
        raise e
    except Exception as e:
        print(f"An error occurred: {e}")
        raise e


@timing_decorator
def save_backdoors(last_produced_clause, backdoors):
    con = get_redis_connection()
    for i, backdoor in enumerate(backdoors):
        key = f'to_minisat:{last_produced_clause + i}'
        value = " ".join(map(str, backdoor)) + " 0"
        con.set(key, value)
    con.close()


@timing_decorator
def push_to_queue_clause(backdoors):
    con = get_redis_connection()
    for i, backdoor in enumerate(backdoors):
        key = f'to_minisat'
        value = " ".join(map(str, backdoor)) + " 0"
        print(f"{key}:{value}")
        con.lpush(key, value)
    con.close()


@timing_decorator
def save_in_drat_file(tmp_dir, learnts_file_name, learnts):
    if not os.path.exists(tmp_dir):
        os.makedirs(tmp_dir)
    path_output = os.path.join(tmp_dir, learnts_file_name)
    if not os.path.exists(path_output):
        # Файл не существует, создаем его и записываем в него
        print(f"Writing {len(learnts)} extracted clauses to new file'{path_output}'...")
        with open(path_output, "w") as file:
            for clause in learnts:
                file.write(" ".join(map(str, clause)) + " 0\n")
    else:
        # Файл существует, дописываем в конец
        print(f"Writing {len(learnts)} extracted clauses to end file '{path_output}'...")
        with open(path_output, "a") as file:
            for clause in learnts:
                file.write(" ".join(map(str, clause)) + " 0\n")
    return path_output


@timing_decorator
def save_learnt(out_file, learnts):
    with open(out_file, "w") as out_file:
        for learnt in learnts:
            # if len(learnt) != 1:
            for c in learnt:
                out_file.write(c + " ")
            out_file.write("0\n")


@timing_decorator
def clean_dir(path_dir: Path):
    files = glob.glob(str(path_dir) + '/*')
    for file in files:
        try:
            if os.path.isdir(file):
                shutil.rmtree(file)
            else:
                os.remove(file)
            print(f'The {file} has been successfully deleted')
        except Exception as e:
            print(f'Error when deleting file {file}: {e}')
            raise e


@timing_decorator
def clean_redis():
    con = get_redis_connection()
    con.flushdb()
    con.close()


@timing_decorator
def check_clauses(clauses, lits, errmsg):
    for clause in clauses:
        id = False
        for c in clause:
            if int(c) in lits:
                id = True
                continue
        assert id, errmsg


print = click.echo

CONTEXT_SETTINGS = dict(help_option_names=["-h", "--help"], max_content_width=999, show_default=True)


@timing_decorator
def _get_learnt_set(learnts, filter_function):
    return set(map(lambda learnt: tuple(sorted(learnt)), filter(filter_function, learnts)))


@timing_decorator
def _get_statistics(derived, learnts):
    origin = _split_clause(learnts)
    derived = _split_clause(derived)

    return {
        "new_units": derived["new_units"] - origin["new_units"],
        "new_binary": derived["new_binary"] - origin["new_binary"],
        "new_ternary": derived["new_ternary"] - origin["new_ternary"],
        "new_large": derived["new_large"] - origin["new_large"],
    }


@timing_decorator
def _split_clause(clauses):
    units = _get_learnt_set(clauses, lambda learnt: len(learnt) == 1)
    binary = _get_learnt_set(clauses, lambda learnt: len(learnt) == 2)
    ternary = _get_learnt_set(clauses, lambda learnt: len(learnt) == 3)
    large = _get_learnt_set(clauses, lambda learnt: len(learnt) > 3)
    return {
        "new_units": units,
        "new_binary": binary,
        "new_ternary": ternary,
        "new_large": large,
    }


@timing_decorator
def sift(minimize_clauses: list[list[int]]):
    minimize_clauses_tuple: set[tuple[int, ...]] = set(map(tuple, map(sorted, minimize_clauses)))
    global CLAUSE_DATABASE
    return minimize_clauses_tuple - CLAUSE_DATABASE


@timing_decorator
def check(clauses, validation_set, prefix):
    for clause in clauses:
        is_sat = False
        for lit in clause:
            is_sat |= (int(lit) in validation_set)
        assert is_sat, prefix


@timing_decorator
def init_combine_cnf(combine_path_cnf: Path, path_cnf: Path):
    copy_file(str(path_cnf), str(combine_path_cnf))


@timing_decorator
def add_learnts(add_clauses: list[list[int]], combine_path_cnf: Path):
    with open(combine_path_cnf, "a") as combine_file:
        for clause in add_clauses:
            combine_file.write(" ".join(map(str, clause)) + " 0\n")


@timing_decorator
def parse_line(line: str):
    pattern = re.compile(
        r"Backdoor \[(\d+(?:, \d+)*)\] of size (\d+) on iter (\d+) with fitness = ([\d.]+), rho = ([\d.]+), hard = (\d+) in ([\d.]+) ms")
    match = pattern.match(line)
    result = dict()
    if match:
        result['backdoor'] = [int(num) for num in match.group(1).split(", ")]
        result['size'] = int(match.group(2))
        result['iteration'] = int(match.group(3))
        result['fitness'] = float(match.group(4))
        result['rho'] = float(match.group(5))
        result['hard'] = int(match.group(6))
        result['time_ms'] = float(match.group(7))
        return result
    else:
        raise Exception("No match")


@timing_decorator
def parse_search_info(backdoors_path: Path):
    results = []
    with open(backdoors_path, "r") as backdoors_file:
        for line in backdoors_file:
            results.append(parse_line(line))
    return results


@timing_decorator
def generate_derive_input_file(backdoors_path: Path, derive_input_path: Path):
    command = f"rg '\[((?:\d+)(?:,\s*\d+)*)\]' {backdoors_path} -or '$1' | sed 's/ //g' > {derive_input_path}"
    process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    stdout, stderr = process.communicate()
    print(command)
    print(stdout)
    print(stderr)


@timing_decorator
def parse_backdoors_path(minimize_file) -> list[list[int]]:
    clauses = [line.split() for line in minimize_file]
    for clause in clauses:
        if clause[-1] != '0':
            raise Exception("Invalid derive format")
    return [list(map(int, clause[:-1])) for clause in clauses]


@timing_decorator
def get_derive_backdoor(
        combine_path_cnf: Path,
        path_tmp_dir: Path,
        ea_num_runs: int,
        ea_instance_size: int,
        ea_num_iters: int,
        mini_conf: int,
        log_dir: Path,
        derive_bin: Path,
        search_bin: Path):
    backdoors_path = find_backdoors(search_bin, path_tmp_dir, combine_path_cnf, ea_num_runs,
                                    ea_instance_size,
                                    ea_num_iters, log_dir)

    copy_to(backdoors_path, log_dir)

    # backdoors_info = parse_search_info(backdoors_path)
    # backdoors = [backdoor_info['backdoor'] for backdoor_info in backdoors_info]
    derive_input_path = path_tmp_dir / 'backdoors.csv'
    generate_derive_input_file(backdoors_path, derive_input_path)

    derive_backdoors_path = derive(derive_bin, combine_path_cnf, derive_input_path, path_tmp_dir, log_dir, mini_conf)

    copy_to(derive_backdoors_path, log_dir)

    with open(derive_backdoors_path, 'r') as derive_file:
        minimize_clauses = parse_backdoors_path(derive_file)
        return minimize_clauses


@timing_decorator
def find_unique_derive(add_clauses, buffer_size, combine_path_cnf, derive_bin, ea_instance_size, ea_num_iters,
                       ea_num_runs, i, last_processed_learnt, mini_conf, path_cnf, path_tmp_dir, read_learnt,
                       root_log_dir, search_bin):
    print(f'Iteration {i}: new learnts: {read_learnt}')
    log_dir = root_log_dir / f"{i}"
    os.makedirs(log_dir)
    add_to_clause_database(sift(add_clauses))
    add_learnts(add_clauses, combine_path_cnf)
    minimize_clauses = get_derive_backdoor(
        combine_path_cnf,
        path_tmp_dir,
        ea_num_runs,
        ea_instance_size,
        ea_num_iters,
        mini_conf,
        log_dir,
        derive_bin,
        search_bin)

    last_processed_learnt += read_learnt
    read_learnt, add_clauses, delete_clauses = get_learnts(last_processed_learnt, buffer_size)
    add_to_clause_database(sift(add_clauses))
    sift_clause = sift(minimize_clauses)
    add_learnts(sift_clause, combine_path_cnf)
    print(f"Iteration {i}: save backdoors")
    push_to_queue_clause(sift_clause)
    return add_clauses, log_dir, minimize_clauses, sift_clause, last_processed_learnt


def save_statistics(minimize_clauses, add_clauses, sift_clause, log_dir):
    with open(log_dir / "statistics", "w") as statistics_file:
        statistics_file.write(f"All minimized clause: {len(minimize_clauses)} \n")
        statistics_file.write(f"Get clause from Reids: {len(add_clauses)} \n")
        statistics_file.write(f"Get derived info: {len(sift_clause)} \n")

        minimize_clauses_split = _split_clause(minimize_clauses)

        for key, learnts_v in minimize_clauses_split.items():
            statistics_file.write(f"deriving {key} where {len(learnts_v)}: {learnts_v} \n")

        global CLAUSE_DATABASE
        derived = _get_statistics(minimize_clauses, CLAUSE_DATABASE)
        for key, learnts_v in derived.items():
            statistics_file.write(f"real deriving unique {key} where {len(learnts_v)}: {learnts_v} \n")

        sift_clause_split = _split_clause(sift_clause)
        for key in derived:
            assert derived[key] == sift_clause_split[
                key], f"sets mast be equals {derived[key]} :: {sift_clause_split[key]}"

        statistics_file.write(f"current time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')} \n")
        global GLOBAL_TIME_FUNCTION_LOG_DICT
        all_time = GLOBAL_TIME_FUNCTION_LOG_DICT.pop("find_unique_derive")
        statistics_file.write(f"calculation time, seconds: {all_time}\n")
        for function_name, time in sorted(GLOBAL_TIME_FUNCTION_LOG_DICT.items(), key=lambda x: x[1], reverse=True):
            statistics_file.write(f"{function_name}={time} seconds: {time / all_time * 100} %\n")


@timing_decorator
def add_to_clause_database(clauses: list[list[int]]):
    global CLAUSE_DATABASE
    CLAUSE_DATABASE.update({tuple(sorted(clause)) for clause in clauses})


@click.command(context_settings=CONTEXT_SETTINGS)
@click.option("--cnf", "path_cnf", required=True, type=click.Path(exists=True), help="File with CNF")
@click.option("--derive-bin", "derive_bin", required=True, type=click.Path(exists=True), help="Path to derive exe file")
@click.option("--search-bin", "search_bin", required=True, type=click.Path(exists=True), help="Path to search exe file")
@click.option("--tmp", "path_tmp_dir", required=True, type=click.Path(exists=False), help="Path temporary directory")
@click.option("--ea-num-runs", "ea_num_runs", default=10, show_default=True, type=int, help="Count backdoors")
@click.option("--random-seed", "seed", default=42, show_default=True, type=int, help="seed")
@click.option("--ea-instance-size", "ea_instance_size", default=10, show_default=True, type=int,
              help="Size of backdoor")
@click.option("--ea-num-iters", "ea_num_iters", default=2000, show_default=True, type=int,
              help="Count iteration for one backdoor")
@click.option("--mini-conf", "mini_conf", default=0, show_default=True, type=int,
              help="count conflict during minimization. If not zero, than deep minimization")
@click.option("--buffer-size", "buffer_size", default=1000, show_default=True, type=int, help="redis buffer size")
@click.option("--root-log-dir", "root_log_dir", required=True, type=click.Path(exists=False),
              help="Path to the root log dir")
@click.option('--redis-host', default='localhost', help='Redis server host')
@click.option('--redis-port', default=6379, help='Redis server port')
def start_producer(path_cnf: str,
                   derive_bin: str,
                   search_bin: str,
                   path_tmp_dir: str,
                   ea_num_runs: int,
                   seed: int,
                   ea_instance_size: int,
                   ea_num_iters: int,
                   mini_conf: int,
                   buffer_size: int,
                   root_log_dir: str,
                   redis_host: str,
                   redis_port: int):
    path_cnf = Path(os.path.abspath(path_cnf))
    derive_bin = Path(os.path.abspath(derive_bin))
    search_bin = Path(os.path.abspath(search_bin))
    path_tmp_dir = Path(os.path.abspath(path_tmp_dir))
    root_log_dir = Path(os.path.abspath(root_log_dir))

    random.seed(seed)

    global HOST, PORT
    HOST = redis_host
    PORT = redis_port

    last_processed_learnt = 0
    os.makedirs(root_log_dir, exist_ok=True)
    os.makedirs(path_tmp_dir, exist_ok=True)
    clean_dir(path_tmp_dir)
    clean_dir(root_log_dir)

    combine_path_cnf = path_tmp_dir / "combine.cnf"
    init_combine_cnf(combine_path_cnf, path_cnf)
    add_to_clause_database(CNF(from_file=path_cnf))

    read_learnt, add_clauses, delete_clauses = get_learnts(last_processed_learnt, buffer_size)

    for i in itertools.count():
        add_clauses, log_dir, minimize_clauses, sift_clause, last_processed_learnt = (
            find_unique_derive(add_clauses, buffer_size,
                               combine_path_cnf, derive_bin,
                               ea_instance_size, ea_num_iters,
                               ea_num_runs, i, last_processed_learnt,
                               mini_conf, path_cnf, path_tmp_dir,
                               read_learnt, root_log_dir, search_bin))
        save_statistics(minimize_clauses, add_clauses, sift_clause, log_dir)
        global GLOBAL_TIME_FUNCTION_LOG_DICT
        GLOBAL_TIME_FUNCTION_LOG_DICT = defaultdict(int)


if __name__ == "__main__":
    start_producer()
