# This script is a utility to extract an SMT and a DIMACS file from the provided linux kernel version
FROM ubuntu:22.04
# Install all packages
RUN apt-get update && apt-get install -y --allow-unauthenticated \
  git \
  python3 python3-pip python3-venv \
  python3-setuptools \
  python3-dev \
  flex \
  bison \
  bc \
  libssl-dev \
  libelf-dev \
  wget \
  build-essential
WORKDIR /home
# Exposing the build argument 'linux_version'; use --build-arg linux_version=<version> to provide a version
ARG linux_version
# Define environment variable that is needed for extracting the right linux kernel version
ENV LINUX_VERSION=$linux_version
RUN git clone https://github.com/paulgazz/kmax.git \
  && cd kmax \
  # Check out the latest tag
  && git checkout $(git describe --tags `git rev-list --tags --max-count=1`) \
  && python3 setup.py install
# Download and create the linux kernel config from the provided version
RUN wget "https://cdn.kernel.org/pub/linux/kernel/v${LINUX_VERSION%%\.*}.x/linux-${LINUX_VERSION}.tar.xz" \
  && tar -xf linux-${LINUX_VERSION}.tar.xz \
  && cd ./linux-${LINUX_VERSION} \
  && make ARCH=x86_64 allnoconfig 
# Extract a DIMACS file
RUN cd ./linux-${LINUX_VERSION} \
  && klocalizer -a x86_64 --save-dimacs /home/linux-${LINUX_VERSION}.dimacs
# Extract an SMT file
RUN cd ./linux-${LINUX_VERSION} \
  && klocalizer -a x86_64 --save-smt /home/linux-${LINUX_VERSION}.smt