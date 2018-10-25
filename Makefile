STACK_NAME = "project-group-x-stack"

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
