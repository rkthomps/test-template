FROM mcr.microsoft.com/vscode/devcontainers/base
ENV HOME=/home/codespace

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="$HOME/.elan/bin:$PATH"
RUN elan --version