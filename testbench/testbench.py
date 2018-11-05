#!/usr/bin/env python3

import os
import sys
import time
from collections import Counter
from itertools import islice

import celery
import docker
from docker import APIClient
import datetime
from celery.utils.log import get_task_logger

CELERY_BROKER_URL = os.environ['CELERY_BROKER_URL']
CELERY_RESULT_BACKEND = os.environ['CELERY_RESULT_BACKEND']

celery_app = celery.Celery(
    "testbench", broker=CELERY_BROKER_URL, backend=CELERY_RESULT_BACKEND)

log = get_task_logger(__name__)

__version__ = 0.1


def convert(str):
    s = str.split(".")
    newstr = s[0] + "." + s[1][0:6]
    format = '%Y-%m-%dT%H:%M:%S.%f'    
    return(datetime.datetime.strptime(newstr, format))


def uppsat(benchmark, timeout):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()

    client.login(username="backeman", password="uppsat")

    client.images.pull("backeman/uppsat:z3")
    
    # Here we have an absolute path
    benchVolume = {'data-volume' : {'bind' : '/benchmarks', 'mode' : 'ro'} }
    env = {'INPUT' : benchmark, 'TIMEOUT' : '30'}

    log.info("Starting UppSAT: %s", env)
    container = client.containers.create("backeman/uppsat:z3", volumes=benchVolume, environment=env)
    container.start()
    ex = container.wait()
    
    # CHECK TIME
    asd =apiclient.inspect_container(resource_id=container.id)
    start = asd['State']['StartedAt']
    end = asd['State']['FinishedAt']
    
    runtime = convert(end) - convert(start)
    
    # CHECK ANSWER
    stdout = container.logs(stdout=True)
    output = "UNKNOWN"
    for l in stdout.decode('ascii').splitlines():
        log.info(l)
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"
            

    # Maybe exception handling...
    # WE ARE DONE!

    log.info("UppSAT: %s %f", output, runtime.total_seconds())
    return (output, runtime.total_seconds())
    
@celery_app.task()
def run_experiment(docker_image, timeout, approximation, benchmark):
    """
    Run an experiment configuration.
    """
    log.warning("Running UppSAT %s %s %s %s", docker_image, timeout, approximation, benchmark)

    return uppsat(benchmark, timeout)


def run_experiments(images, timeout, approximations, benchmarks):
    """
    Spawn tasks to run experiments.

    Returns a task group.
    """
    
    #configs = cartesian_product(images, approximations, benchmarks)
    configs = [("uppsat:z3", "ijcar", "IJCAR2018/mult1.c.10.smt2"), ("uppsat:z3", "ijcar", "IJCAR2018/e2a_1.c.smt2")]

    
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
        r
        for r in [subtask.result for subtask in task.results if subtask.ready]
    ]


def launch_benchmarks(dir):
    timeout = 5
    configs = []
    for f in os.listdir(dir):
        image = "uppsat:z3"
        approx = "ijcar"
        bm = dir + f
        print("Adding: %s %s %s" % (image, approx, bm))
        newConfig = (image, approx, bm)
        configs.append(newConfig)

    tasks = (run_experiment.s(image, timeout, approximation, benchmark)
             for (image, approximation, benchmark) in configs)
    group = celery.group(tasks)()
    group.save()
    return group        

if __name__ == '__main__':
    directory = sys.argv[1]
    group = launch_benchmarks(directory)
    print(group)
    # print(summarise_results(group))
