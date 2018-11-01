#!/usr/bin/env python3

from flask import Flask
from flask_restplus import Api, Resource, fields

#import testbench

# POST /experiments
# {"benchmarks: [str]",
#  "timeout": int,
#  "approximations": [""],
#  "solvers": ["backeman/uppsat:z3", "backeman/uppsat:mathsat"]}
#
# > <ID>
# Runs the set of experiments: benchmarks x approximations x solvers

# GET /experiments/<ID>/status
# {
# "status" = {DONE, NOT DONE, ERROR}
# "experiment_configuration_count" = int
# "results" = [([SAT|UNSAT|UNKNOWN, Runtime])]
# "errored_configurations" = [(benchmark, solver, approximation)]
# }

# GET /experiments/<ID>/table
# Nice HTML table
app = Flask(__name__)
api = Api(app)

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
    })


@api.route('/experiments')
class SubmitExperiment(Resource):
    @api.expect(submission_model)
    def post(self):
        pass


@api.route('/experiments/<string:id>/status')
class ExperimentResult(Resource):
    @api.marshal_with(result_model)
    def get(self, id):
        pass

    def delete(self, id):
        pass


@api.route('/experiments/<string:id>/table')
class ExperimentResultTable(Resource):
    def get(self, id):
        pass


if __name__ == '__main__':
    app.run(host='0.0.0.0', debug=True)
