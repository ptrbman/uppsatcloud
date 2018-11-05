#!/usr/bin/env python3

import logging
import pprint

import daiquiri
from flask import Flask, redirect, url_for
from flask_restplus import Api, Resource, fields

import testbench

app = Flask(__name__)
api = Api(app, validate=True)
daiquiri.setup(level=logging.INFO)
log = daiquiri.getLogger(__name__)

HTTP_STATUS_ACCEPTED = 202
HTTP_STATUS_NOT_FOUND = 404

approximation_field = fields.String(
    example="FIX ME!!!",
    description="An approximation configuration parameter for UppSAT")
solver_field = fields.String(
    example="backeman/uppsat:z3", description="A Docker tag for a solver")

submission_model = api.model(
    'Experiments Submission', {
        'benchmarks':
        fields.List(
            fields.String(
                example=("(define-fun _t_28 () Bool (and _t_25 _t_27))\n"
                         "(assert _t_28)\n"
                         "(check-sat)")),
            description="A list of benchmarks in X format to run"),
        'timeout':
        fields.Integer(example=60, description="The timeout, in seconds"),
        'approximations':
        fields.List(
            approximation_field,
            description="A list of approximation settings for UppSAT"),
        'solvers':
        fields.List(solver_field, description="A list of solvers to run"),
    })

benchmark_name_field = fields.String(
    example="my-benchmark.sat", description="The name of a benchmark file")

configuration_field = fields.Nested(
    api.model(
        'Configuration Triplet', {
            'benchmark': benchmark_name_field,
            'solver': solver_field,
            'approximation': approximation_field
        }))

result_field = fields.Nested(
    api.model(
        'Single-experiment Result', {
            'result':
            fields.String(
                example="UNSAT",
                description="One of SAT, UNSAT, UNKNOWN, or ERROR"),
            'runtime':
            fields.Float(description="The runtime, in seconds"),
            'benchmark':
            benchmark_name_field,
            'solver':
            solver_field,
            'approximation':
            approximation_field,
        }))

result_model = api.model(
    'Experiments Result', {
        'status':
        fields.String(
            description="A status; one of DONE, RUNNING or ERROR",
            example="RUNNING"),
        'experiment_count':
        fields.Integer,
        'results':
        fields.List(result_field),
        'errors':
        fields.List(
            configuration_field,
            description="A list of errored configurations"),
        'id':
        fields.String(description="The ID of the given task"),
    })


@api.route('/experiments')
class SubmitExperiment(Resource):
    @api.expect(submission_model)
    def post(self):
        setup = api.payload
        log.info("Got POST with {}".format(pprint.pformat(setup)))

        task = testbench.run_experiments(
            images=setup['solvers'],
            timeout=setup['timeout'],
            approximations=setup['approximations'],
            benchmarks=setup['benchmarks'])

        # This is what produces a stable ID, so it's important!
        task.save()

        return redirect(url_for('experiment_result', id=task.id))


def task_exists(task):
    if not task:
        return False

    return True


@api.route('/experiments/<string:id>')
class ExperimentResult(Resource):
    @api.marshal_with(result_model)
    def get(self, id):
        log.info("Getting task ID {}".format(id))

        task = testbench.celery_app.GroupResult.restore(id)
        if not task_exists(task):
            return "Task not found: {}".format(id), HTTP_STATUS_NOT_FOUND

        completed_results = testbench.summarise_results(task)
        log.info("Got results {}".format(pprint.pformat(completed_results)))

        results = []
        errors = []
        for (result, runtime), (solver, approx,
                                benchmark) in completed_results:
            config_triplet = {
                'benchmark': benchmark,
                'solver': solver,
                'approximation': approx
            }

            if result == "ERROR":
                errors.append(config_triplet)
            else:
                results.append({
                    'result': result,
                    'runtime': runtime,
                    **config_triplet
                })

        if task.failed():
            log.error("Failed task {}: {}".format(task_id, task.results))
            status = "FAILED"
        else:
            status = "COMPLETED" if task.ready() else "PENDING"

        return {
            'id': id,
            'status': status,
            'experiment_count': len(task.results),
            'completed_count': task.completed_count(),
            'results': results,
            'errors': errors,
        }

    def delete(self, id):
        task = testbench.celery_app.GroupResult.restore(id)
        if not task_exists(task):
            return "Task not found: {}".format(id), HTTP_STATUS_NOT_FOUND
        task.revoke(terminate=True)
        task.forget()
        task.delete()


@api.route('/experiments/<string:id>/table')
class ExperimentResultTable(Resource):
    def get(self, id):
        pass


if __name__ == '__main__':
    app.run(host='0.0.0.0', port="5000", debug=True)
