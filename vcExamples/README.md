# Vulnerable Component Limits Protocol Strength



## Target platform

| Component | Place | Role | Corruptible | Depends on |
| --- | --- | --- | --- | --- |
| `rtm` | `hw` | Hardware root of trust for measurement | no | |
| `mm` | `hv` | Protected meta-measurer | yes | |
| `lkim` | `ma` | Linux Kernel Integrity Measurer | yes | |
| `vcm` | `ma` | Virus checker monitor | yes | |
| `ker` | `us` | Linux kernel | yes |
| `vc` | `us` | Virus checker | yes | `ker` |
| `sys` | `us` | The parts of the system scanned by the virus checker | yes | |


## Protocols

| Name | Protocol | Description |
| --- | --- | --- |
| `P2` | `ms(mm,lkim) +<+ ms(mm,vcm) +<+ ms(lkim,ker) +<+ ms(vcm,vc) +<+ ms(vc,sys)` | Uses meta-measurer. |
| `P3` | `ms(rtm,lkim) +<+ ms(rtm,vcm) +<+ ms(lkim,ker) +<+ ms(vcm,vc) +<+ ms(vc,sys)` | Uses rtm. |


## Adversary ordering

| Name | Assumptions |
| --- | --- |
| `Baseline` | `c(vc) <= c(ker),  c(vc) <= c(vcm),  c(vcm) <= c(lkim)` | 
| `Vulnerable vc` | `c(vc)^t <= c(mm),  baseline` |

`Vulnerable vc` ordering assumes that the meta-measurer on the target platform is well-protected while the virus checker is vulnerable Therefore, corrupting the virus checker even within a limited time frame is easier than corrupting the meta-measurer.

## Results

| Result | Adversary Ordering | |
| --- | --- | --- | 
| `P2 <= P3` | `baseline` | Replacing `mm` with `rtm` strengthens the protocol as expected |
| `P2 = P3` | `vulnerable vc` | `vc` is the weak point nullying the benefit of choosing `rtm` over a sufficiently-protected `mm` |

