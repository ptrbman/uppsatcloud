STACK_NAME = "project-group-x-stack"
NR_WORKERS_DEV = 1
DOCKER_REPO=backeman/uppsat
WORKER_TAG=${DOCKER_REPO}:worker
API_TAG=${DOCKER_REPO}:api

all: build-images

.PHONY: stack
stack:
	openstack stack create \
		--enable-rollback \
		--wait \
		--template stack.yaml ${STACK_NAME}

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


push-images:
	docker push ${API_TAG}
	docker push ${WORKER_TAG}

validate-stack:
	openstack stack create \
	--dry-run \
	--template stack.yaml ${STACK_NAME}
