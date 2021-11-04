FROM ubuntu:20.04
ARG jenkins_id
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update -y &&\
    apt-get install -y git curl build-essential unzip bubblewrap rsync libgmp-dev &&\
    echo '\ny\n' | bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)" &&\
    useradd -m jenkins -u ${jenkins_id}
USER jenkins
RUN opam init -y &&\
    opam install -y dune ppx_import ppx_yojson_conv qcheck zarith dune-build-info
  
