tools     = mason
services  = foreman
egress    = true
test      = git submodule update --init --recursive && make test
threshold = 64
