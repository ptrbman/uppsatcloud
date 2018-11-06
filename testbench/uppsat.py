def uppsat(benchmark):
    ### RUN UppSAT
    client = docker.from_env()
    apiclient = APIClient()

    client.login(username="backeman", password="uppsat")

    client.images.pull("backeman/uppsat:z3")
    
    # Here we have an absolute path
    benchVolume = {'data-volume' : {'bind' : '/benchmarks', 'mode' : 'ro'} }
    
    container = client.containers.create("backeman/uppsat:z3", "/benchmarks/" + benchmark, volumes=benchVolume)
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
        if l.strip() == "sat":
            output = "SAT"
        elif l.strip() == "unsat":
            output = "UNSAT"
            

    # Maybe exception handling...
    # WE ARE DONE!
    log.info("UppSAT: %s %f", output, runtime.total_seconds())
    return (output, runtime.total_seconds())
