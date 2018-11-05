#!/usr/bin/env python3

import datetime
import os
import time
import uuid
from collections import Counter
from contextlib import contextmanager
from itertools import islice

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


def uppsat(benchmark):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()
    log.info("Running UppSAT on benchmark {}".format(benchmark))

    client.login(username="backeman", password="uppsat")

    client.images.pull("backeman/uppsat:z3")

    # Here we have an absolute path
    benchVolume = {'data-volume': {'bind': BENCHMARK_ROOT, 'mode': 'ro'}}

    container = client.containers.create(
        "backeman/uppsat:z3",
        os.path.join(BENCHMARK_ROOT, benchmark),
        volumes=benchVolume)
    container.start()
    ex = container.wait()

    # CHECK TIME
    asd = apiclient.inspect_container(resource_id=container.id)
    start = asd['State']['StartedAt']
    end = asd['State']['FinishedAt']

    runtime = dateparser.parse(end) - dateparser.parse(start)

    # CHECK ANSWER
    stdout = container.logs(stdout=True)
    output = "UNKNOWN"
    for l in stdout.decode('ascii').splitlines():
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"

    # Maybe exception handling...
    # WE ARE DONE!
    log.info("UppSAT: %s %f", output, runtime.total_seconds())
    return (output, runtime.total_seconds())


@celery_app.task(retries=3)
def run_experiment(docker_image, timeout, approximation, benchmark):
    """
    Run an experiment configuration.
    """
    log.warning("Running UppSAT %s %s %s %s", docker_image, timeout,
                approximation, benchmark)
    with temporary_benchmark(benchmark) as benchmark_file:
        return (uppsat(benchmark_file), (docker_image, approximation,
                                         benchmark))


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

    #configs = cartesian_product(images, approximations, benchmarks)
    configs = [("uppsat:z3", "ijcar", """
                ;; activate model generation
                (set-option :produce-models true)
                (declare-fun x () Int)
                (declare-fun y1 () Int)
                (declare-fun y2 () Int)
                (declare-fun z () Int)
                (assert (= x y1))
                (assert (not (= y1 z)))
                (assert (= x y2))
                (assert (and (> y2 0) (< y2 5)))
                (check-sat)
                (get-value (x z))
                (exit)
                """),
               ("uppsat:z3", "ijcar", """
                (set-option :produce-unsat-cores true)
                (declare-fun x () Int)
                (declare-fun y1 () Int)
                (declare-fun y2 () Int)
                (declare-fun z () Int)
                (define-fun A1 () Bool (= x y1))
                (define-fun A2 () Bool (not (< z 0)))
                (define-fun A3 () Bool (= y1 z))
                (define-fun B () Bool (and (= x y2) (not (= y2 z))))
                (assert (! A1 :named First))
                (assert (! A2 :named Second))
                (assert (! A3 :named Third))
                (assert B)
                (check-sat)
                (get-unsat-core)
                (exit)
                """),
               ("uppsat:z3", "ijcar", """
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun a () Bool)
                (declare-fun b () Bool)
                (declare-fun c () Bool)
                (declare-fun d () Bool)
                (assert (= (> (+ x y) 0) a))
                (assert (= (< (+ (* 2 x) (* 3 y)) (- 10)) c))
                (assert (and (or a b) (or c d)))
                (check-allsat (a b))
                (exit)
                """)]

    tasks = (run_experiment.s(image, timeout, approximation, benchmark)
             for (image, approximation, benchmark) in configs)
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


if __name__ == '__main__':
    # run_experiments("ubuntu:latest", 17, ["hej"])
    group = run_experiments("uppsat:z3", 60, "ijcar", "test.smt2")
    print(group)
    print(summarise_results(group))
