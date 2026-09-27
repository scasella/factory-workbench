# Protected verifier/runtime image: pinned Lean base + pre-built protected
# Factory library + fixed harness. Not candidate-editable.
ARG BASE=factory-lean-base:v4.34.1
FROM ${BASE}
USER root
RUN mkdir -p /opt/factory /opt/harness /work /in /out && chown builder:builder /opt/factory /work /out
COPY --chown=builder:builder lean/lean-toolchain lean/lakefile.toml lean/Factory.lean /opt/factory/
COPY --chown=builder:builder lean/Factory /opt/factory/Factory
COPY verifier/harness/ /opt/harness/
RUN chmod 0755 /opt/harness/*.sh
USER builder
RUN cd /opt/factory && lake build Factory Factory:static factory-kernel
USER root
RUN chown -R root:root /opt/factory && chmod -R a-w /opt/factory /opt/harness
USER builder
WORKDIR /work
