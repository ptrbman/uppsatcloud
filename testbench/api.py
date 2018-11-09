#!/usr/bin/env python3

import logging
import pprint
import sys

import daiquiri
import requests
from flask import Flask, Response, redirect, url_for
from flask_restplus import Api, Resource, fields

import testbench

app = Flask(__name__)
api = Api(app, validate=True)
daiquiri.setup(level=logging.INFO)
log = daiquiri.getLogger(__name__)

HTTP_STATUS_ACCEPTED = 202
HTTP_STATUS_NOT_FOUND = 404

approximation_field = fields.String(
    example="ijcar",
    description="An approximation configuration parameter for UppSAT")
solver_field = fields.String(
    example="backeman/uppsat:z3", description="A Docker tag for a solver")

submission_model = api.model(
    'Experiments Submission', {
        'benchmarks':
        fields.List(
            fields.String(example="square.smt2"),
            description=
            "A list of names of benchmarks files in SMTLib format to run"),
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


def getJSON(id):
    json = requests.get("http://130.238.29.80/experiments/" + id).json()
    return json


def extractBenchmarks(json):
    benchmarks = []
    for res in json['results']:
        benchmarks.append(res['benchmark'])
    return benchmarks


def jsonsToDicts(jsons, benchmarks):
    dicts = []
    for j in jsons:
        d = {}
        for r in j['results']:
            d[r['benchmark']] = (r['result'], r['runtime'])
        dicts.append(d)
    return dicts


def jsonToDict(json):
    d = {}
    for r in json['results']:
        d[r['benchmark']] = (r['result'], r['runtime'])
    return d


def table(benchmarks, titles, dicts):
    top = ""
    top += "<html>\n"

    style = """<style>
#data {
    font-family: "Trebuchet MS", Arial, Helvetica, sans-serif;
    border-collapse: collapse;
    width: 100%;
}

#data td, #data th {
    border: 1px solid #ddd;
    padding: 8px;
}

#data tr:nth-child(even){background-color: #f2f2f2;}

#data tr:hover {background-color: #ddd;}

#data th {
    padding-top: 12px;
    padding-bottom: 12px;
    text-align: left;
    background-color: #4CAF50;
    color: white;
}
</style>"""

    header = "<table id=\"data\">\n"
    header += "<tr><th>Benchmarks</th>\n"
    for t in titles:
        header += "<th>" + t + "</th>\n"
    header += "</tr>\n"

    body = ""
    for b in benchmarks:
        best = -1
        besttime = -1
        for i in range(len(dicts)):
            time = dicts[i][b]
            if time != "T/O" and (besttime == -1 or time < besttime):
                besttime = time
                best = i

        body += "<tr>\n"
        body += "<td>" + b + "</td>\n"
        results = []
        for i in range(len(dicts)):
            time = dicts[i][b]
            if i == best:
                body += "<td><b>" + str(time) + "</b></td>\n"
            else:
                body += "<td>" + str(time) + "</td>\n"
        body += "</tr>\n"

    footer = "</table>\n"
    footer += "</html>\n"

    return (top + style + header + body + footer)


@api.route('/experiments/<string:id1>/<string:id2>/table')
class ExperimentResultTable(Resource):
    def get(self, id1, id2):
        id1res = testbench.summarise_results(
            testbench.celery_app.GroupResult.restore(id1))
        id2res = testbench.summarise_results(
            testbench.celery_app.GroupResult.restore(id2))

        benchmarks = []

        dict1 = {}
        for (result, runtime), (solver, approx, benchmark) in id1res:
            benchmarks.append(benchmark)
            if (result == "SAT" or result == "UNSAT"):
                dict1[benchmark] = runtime
            else:
                dict1[benchmark] = "T/O"

        dict2 = {}
        for (result, runtime), (solver, approx, benchmark) in id2res:
            if (result == "SAT" or result == "UNSAT"):
                dict2[benchmark] = runtime
            else:
                dict2[benchmark] = "T/O"

        log.info("html")
        html = table(benchmarks, [id1, id2], [dict1, dict2])
        log.info(html)

        r = Response(html, mimetype="text/html")

        r.status_code = 200
        return r


@api.route('/config/workers')
class WorkerCount(Resource):
    def get(self):
        return len(
            [w for w in testbench.get_workers() if testbench.worker_active(w)])


@api.route('/config/workers/<string:nr_workers>')
class WorkerCount(Resource):
    def put(self, nr_workers):
        testbench.scale_workers(int(nr_workers))
        return {}


if __name__ == '__main__':
    app.run(host='0.0.0.0', port="5000", debug=True)
