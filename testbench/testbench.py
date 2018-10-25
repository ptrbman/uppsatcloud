#!/usr/bin/env python3

import os
import time
from collections import Counter
from itertools import islice

import celery

CELERY_BROKER = os.environ['CELERY_BROKER']
CELERY_RESULT_BACKEND = os.environ['CELERY_RESULT_BACKEND']

celery_app = celery.Celery(
    "pronouns", broker=CELERY_BROKER, backend=CELERY_RESULT_BACKEND)

__version__ = 0.1


@celery_app.task()
def run_experiment(docker_image, timeout, instances):
    """
    Run an experiment configuration.
    """

    # This is where we call the Docker API etc and Do The Thing.

    return None


def run_experiments(configurations):
    """
    Spawn tasks to run experiments.

    FIXME: This doesn't unpack anything.

    Returns a task group.
    """
    paths = os.listdir(TWEET_DATA_PATH)

    tasks = (run_experiment.s(None) for configuration in configurations)
    return celery.group(tasks)()


def summarise_results(task):
    """
    Helper function to summarise and extract the data from a task.

    It's non-blocking and will ignore any non-finished sub-tasks.
    """

    return [
        r for r in [subtask.result for subtask in task.results if subtask.ready]
    ]



if __name__ == '__main__':
    print("Do something here!")
