import sys

print("//================\\\\")
print("||  UppSAT script ||")
print("\\\\================//")

input=sys.argv[1]
print("Input: " + input)

import docker
from docker import APIClient

### RUN UppSAT
client = docker.from_env()
apiclient = APIClient()

# Here we have an absolute path
benchVolume = {'/benchmarks' : {'bind' : '/benchmarks', 'mode' : 'ro'} }

container = client.containers.create("z3:latest", "/benchmarks/" + input, volumes=benchVolume)
container.start()
ex = container.wait()

# CHECK TIME
asd =apiclient.inspect_container(resource_id=container.id)
start = asd['State']['StartedAt']
end = asd['State']['FinishedAt']

import datetime
def convert(str):
    s = str.split(".")
    newstr = s[0] + "." + s[1][0:6]
    format = '%Y-%m-%dT%H:%M:%S.%f'    
    return(datetime.datetime.strptime(newstr, format))

runtime = convert(end) - convert(start)

# CHECK ANSWER
stdout = container.logs(stdout=True)
output = "UNKNOWN"
for l in stdout.decode('ascii').splitlines():
    if l.strip() == "sat":
        output = "SAT"
    elif l.strip() == "unsat":
        output = "UNSAT"


# WE ARE DONE!        
print((output, runtime.total_seconds()))
# except docker.errors.ContainerError:

