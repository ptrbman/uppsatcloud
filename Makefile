STACK_NAME = "project-group-x-stack"
NR_WORKERS_DEV = 8

.PHONY: stack
stack:
	openstack stack create \
		--create-rollback \
		--wait \
		--template stack.yaml ${STACK_NAME}

	openstack stack output show ${STACK_NAME} \
		master_instance_floating_ip \
		--format=value \
		--column=output_value

report/report.pdf:
	cd report && $(MAKE) report.pdf


.PHONY: start-local
start-local:
	docker-compose down
	docker-compose up \
				--build \
				--scale worker=${NR_WORKERS_DEV}
