#!/usr/bin/env python3

import os
import time
from collections import Counter
from itertools import islice

import celery
import docker
from celery.utils.log import get_task_logger

CELERY_BROKER = os.environ['CELERY_BROKER']
CELERY_RESULT_BACKEND = os.environ['CELERY_RESULT_BACKEND']

celery_app = celery.Celery(
    "testbench", broker=CELERY_BROKER, backend=CELERY_RESULT_BACKEND)

log = get_task_logger(__name__)

__version__ = 0.1


@celery_app.task()
def run_experiment(docker_image, timeout, instances):
    """
    Run an experiment configuration.
    """

    client = docker.from_env()

    log.warning("Getting image %s", docker_image)
    client.images.pull(docker_image)
    log.warning("Fetched image %s", docker_image)
    print("hello")

    return None


def run_experiments(image, timeout, instances):
    """
    Spawn tasks to run experiments.

    Returns a task group.
    """

    tasks = (run_experiment.s(image, timeout, instance)
             for instance in instances)
    return celery.group(tasks)()


def summarise_results(task):
    """
    Helper function to summarise and extract the data from a task.

    It's non-blocking and will ignore any non-finished sub-tasks.
    """

    return [
        r
        for r in [subtask.result for subtask in task.results if subtask.ready]
    ]


if __name__ == '__main__':
    run_experiments("ubuntu", 17, ["hej"])
