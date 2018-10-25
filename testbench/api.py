#!/usr/bin/env python3

from flask import Flask
from flask_restplus import Resource, Api

#import testbench

app = Flask(__name__)
api = Api(app)

HTTP_STATUS_ACCEPTED = 202
HTTP_STATUS_NOT_FOUND = 404

@api.route('/hello')
class HelloWorld(Resource):
    @api.doc(description="Say hi!",
             id='hi')
    def get(self):
        return {'hello': 'world'}

if __name__ == '__main__':
    app.run(host='0.0.0.0', debug=True)
