# Trusted Execution Environment Attestation Through a Cloud Proxy

Investigates the relative strength of direct Trusted Execution Environment (TEE) attestation and proxy-mediated attestation.

## Target platform

| Component | Place | Role | Corruptible | Depends on |
| --- | --- | --- | --- | --- |
| `rtm` | `hw` | Hardware root of trust for measurement | no | |
| `swk` | `sw` | Secure-world kernel | yes | |
| `appm` | `sw` | TEE-resident application measurer | yes | `swk` |
| `nwk` | `nw` | Normal-world kernel | yes | |
| `rtlib` | `nw` | Attestation client library, shipped in the proxy service's SDK | yes | `nwk` |
| `app` | `nw` | The application being attested | yes | |
| `pxy` | `atp` | Cloud proxy service | yes | |


## Protocols

| Name | Protocol | Description |
| --- | --- | --- |
| `P1` | `ms(rtm,appm) +<+ ms(appm,app)` | Direct TEE |
| `P2` | `ms(pxy,rtlib) +<+ ms(rtm,appm) +<+ ms(appm,rtlib) +<+ ms(rtlib,app)` | Proxy-mediated |
| `P3` | `ms(rtm,appm) +<+ ms(appm,rtlib) +<+ ms(rtlib,app)`| Without proxy |
| `P4` | `ms(pxy,rtlib) +<+ ms(rtm,appm) +<+ ms(appm,app) +<+ ms(appm,rtlib) +<+ ms(rtlib,app)` | Direct and proxy |


## Adversary ordering

Corrupting normal-world components is easier than secure-world components.

`c(nwk) <= c(swk),  c(rtlib) <= c(appm)`

## Results

| Result | |
| --- | --- | 
| `P1 >= P2` | Proxy-mediated is worse than direct TEE |
| `P2 = P3` | The proxy's check adds nothing |
| `P1 <= P4` | Restoring the direct measurement of `app` reverses the regression

## Reproducing
```
(cd scripts/ ; bash setup.sh teeExamples)
make
```