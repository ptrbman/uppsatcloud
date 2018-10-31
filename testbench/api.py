#!/usr/bin/env python3

from flask import Flask
from flask_restplus import Api, Resource

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


@api.route('/hello')
class HelloWorld(Resource):
    @api.doc(description="Say hi!")
    def get(self):
        return {'hello': 'world'}


if __name__ == '__main__':
    app.run(host='0.0.0.0', debug=True)
