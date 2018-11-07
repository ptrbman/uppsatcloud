STACK_NAME = "project-group-x-stack"
NR_WORKERS_DEV = 5
DOCKER_REPO=backeman/uppsat
WORKER_TAG=${DOCKER_REPO}:worker
API_TAG=${DOCKER_REPO}:api

all: build-images

.PHONY: stack
stack:
	openstack stack create \
		--wait \
		--parameter nr_workers=1 \
		--template stack.yaml ${STACK_NAME}

	openstack stack output show ${STACK_NAME} \
		--all \
		--fit-width

update-stack:
	openstack stack update \
		--wait \
		--parameter nr_workers=1 \
		--template stack.yaml ${STACK_NAME}

.PHONY: get-master-ip
get-master-ip:
	openstack stack output show ${STACK_NAME} \
			master_instance_floating_ip \
			--format=value \
			--column=output_value

.PHONY: report
report:
	cd report && $(MAKE) report.pdf


.PHONY: start-local
start-local:
	docker-compose down
	docker-compose up \
				--build \
				--scale worker=${NR_WORKERS_DEV}

.PHONY: clean
clean:
	openstack stack delete --wait ${STACK_NAME}

build-images:
	cd testbench && docker build \
			--file Dockerfile.worker \
			--tag ${WORKER_TAG} .

	cd testbench && docker build \
			--file Dockerfile.api \
			--tag ${API_TAG} .

	cd uppsat-docker && docker build \
			--file Dockerfile.z3 \
			--tag ${DOCKER_REPO}:z3 .

	cd uppsat-docker && docker build \
			--file Dockerfile.mathsat \
			--tag ${DOCKER_REPO}:mathsat .

push-images:
	docker push ${API_TAG}
	docker push ${WORKER_TAG}
	docker push ${DOCKER_REPO}:z3
	docker push ${DOCKER_REPO}:mathsat

validate-stack:
	openstack stack create \
	--dry-run \
	--template stack.yaml ${STACK_NAME}
