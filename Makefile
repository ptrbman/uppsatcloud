STACK_NAME = "project-group-x-stack"
NR_WORKERS_DEV = 1

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
