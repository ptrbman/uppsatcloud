#!/usr/bin/env python3

import csv
import datetime
import itertools
import os
import pprint
import sys
import time
import uuid
from collections import Counter
from contextlib import contextmanager

import logging
import celery
import dateparser
import docker
from celery.utils.log import get_task_logger
from docker import APIClient

CELERY_BROKER_URL = os.environ['CELERY_BROKER_URL']
CELERY_RESULT_BACKEND = os.environ['CELERY_RESULT_BACKEND']
BENCHMARK_ROOT = "/benchmarks"

celery_app = celery.Celery(
    "testbench", broker=CELERY_BROKER_URL, backend=CELERY_RESULT_BACKEND)

log = get_task_logger(__name__)

__version__ = 0.1


def uppsat(docker_image, benchmark, timeout, approximation):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()
    log.info("Running UppSAT on benchmark {}".format(benchmark))

    client.login(username="backeman", password="uppsat")
    client.images.pull(docker_image)

    # Here we have an absolute path
    benchVolume = {'data-volume': {'bind': BENCHMARK_ROOT, 'mode': 'ro'}}
    env = {
        'INPUT': os.path.join(BENCHMARK_ROOT, benchmark),
        'TIMEOUT': timeout,
        'APPROXIMATION': approximation
    }

    container = client.containers.run(
        docker_image, environment=env, volumes=benchVolume, detach=True)
    log.info("Started container {}".format(container.id))

    ex = container.wait()
    # CHECK TIME
    cInfo = apiclient.inspect_container(resource_id=container.id)
    start = cInfo['State']['StartedAt']
    end = cInfo['State']['FinishedAt']

    runtime = dateparser.parse(end) - dateparser.parse(start)

    # CHECK ANSWER
    stdout = container.logs(stdout=True)
    output = "TIMEOUT"
    for l in stdout.decode('ascii').splitlines():
        log.info(l)
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"
        elif "rror" in l.strip():
            output = "ERROR"

    # Maybe exception handling...

    log.info("UppSAT: %s %f", output, runtime.total_seconds())
    log.info("Removing container {}".format(container.id))
    container.remove()
    return (output, runtime.total_seconds())


@celery_app.task(retries=3)
def run_experiment(docker_image, timeout, approximation, benchmark):
    """
    Run an experiment configuration.
    """
    log.warning("Running UppSAT %s %s %s %s", docker_image, timeout,
                approximation, benchmark)
    with temporary_benchmark(benchmark) as benchmark_file:
        uppsat_result = uppsat(
            docker_image=docker_image,
            benchmark=benchmark_file,
            timeout=timeout,
            approximation=approximation)
        return (uppsat_result, (docker_image, approximation, benchmark))


@celery_app.task(retries=3)
def run_experiment_file(docker_image, timeout, approximation, benchmark_file):
    """
    Run an experiment configuration.
    """
    log.warning("Running UppSAT %s %s %s %s", docker_image, timeout,
                approximation, benchmark_file)
    return (uppsat(docker_image, benchmark_file, timeout, approximation),
            (docker_image, approximation, benchmark_file))


@contextmanager
def temporary_benchmark(benchmark):
    """
    Dump a benchmark to file, taking care to remove it afterwards.
    """
    # Make a temporary file name
    filename = "{}.smt2".format(uuid.uuid4())
    full_path = os.path.join(BENCHMARK_ROOT, filename)
    log.info("Serialised benchmark to file {}".format(full_path))
    with open(full_path, 'w') as fp:
        fp.write(benchmark)
        # Super flush the file
        fp.flush()
        os.fsync(fp.fileno())
    try:
        yield filename
    finally:
        os.remove(full_path)


def run_experiments(images, timeout, approximations, benchmarks):
    """
    Spawn tasks to run experiments.

    Returns a task group.
    """

    # The set is needed to remove duplicates:
    configs = set(
        itertools.product(images, [timeout], approximations, benchmarks))

    log.info("Generated instance set: %s", pprint.pformat(configs))

    tasks = (run_experiment.s(*config) for config in configs)
    group = celery.group(tasks)()
    group.save()
    return group


def summarise_results(task):
    """
    Helper function to summarise and extract the data from a task.

    It's non-blocking and will ignore any non-finished sub-tasks.
    """

    return [
        r for r in [
            subtask.result for subtask in task.results
            if (subtask.ready and subtask.result)
        ]
    ]


def launch_benchmarks_no_celery(dir, backend, approximation, timeout, copies, file_name):
    configs = []
    for f in os.listdir(dir):
        image = "backeman/uppsat:" + backend
        bm = os.path.join(dir, f)
        print("Adding: %s %s %s" % (image, approximation, bm))
        newConfig = (image, approximation, bm)
        configs.append(newConfig)

    results = []

    with open(file_name, "a") as fp:
        writer = csv.writer(fp)
        for _ in range(copies): 
            for (image, approximation, benchmark) in configs:
                (result, runtime), _ = run_experiment_file(
                    image, timeout, approximation, benchmark)

                writer.writerow([benchmark, result, runtime])
                results.append([benchmark, result, runtime])
    return results    

def launch_benchmarks(dir, backend, approximation, timeout, copies):
    configs = []
    for f in os.listdir(dir):
        image = "uppsat:" + backend
        bm = os.path.join(dir, f)
        print("Adding: %s %s %s" % (image, approximation, bm))
        newConfig = (image, approximation, bm)
        configs.append(newConfig)

    groups = []

    for _ in range(copies):
        tasks = (run_experiment_file.s(image, timeout, approximation,
                                       benchmark)
                 for (image, approximation, benchmark) in configs)
        group = celery.group(tasks)()
        group.save()
        groups.append(group)

    return groups


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: tesbench.py directory [backend=z3] [approximation=ijcar] [timeout=5] [copies=1]")
        print("\tbackend: z3 | mathsat")
        print("\tapproximation: ijcar | fixedpoint")
        import sys
        sys.exit(0)

    log = logging.getLogger()
    logging.basicConfig(level=logging.INFO)
        
    directory = sys.argv[1]

    # csv_file_name = sys.argv[2]

    backend = "z3"
    if len(sys.argv) >= 3:
        backend = sys.argv[2]
    
    approximation = "ijcar"
    if len(sys.argv) >= 4:
        approximation = sys.argv[3]
    
    timeout = 5
    if len(sys.argv) >= 5:
        timeout = int(sys.argv[4])

    copies = 1
    if len(sys.argv) >= 6:
        copies = int(sys.argv[5])

    csv_file_name = "output.csv"       
    if len(sys.argv) >= 7:
        csv_file_name = sys.argv[6]

    # groups = launch_benchmarks(directory, backend, approximation, timeout,
    groups = launch_benchmarks_no_celery(directory, backend, approximation, timeout, copies, csv_file_name)     
    # for g in groups:
    #     print(g.id)
    # print(summarise_results(group))
