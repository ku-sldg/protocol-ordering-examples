# System Management Mode and Static vs Dynamic Root of Trust

Investigates the relative strength of Intel TXT's dynamic and static chains of trust 
as well as the attacks on Intel Trusted Execution Technology (TXT) that motivated
the SMI transfer monitor (STM).

The former portion of this example evaluates distinct measurement chains with a common
weakness, while the latter evaluates measuring a component versus containing it.

## Target platform

| Component | Place | Role | Corruptible | Depends on |
| --- | --- | --- | --- | --- |
| `crtm` | `hw` | Core root of trust for measurement | no | |
| `cpu` | `hw` | The CPU's measured launch instruction | no | |
| `bios` | `fw` | Platform firmware | yes | |
| `smm` | `fw` | System management mode handler | yes | |
| `boot` | `os` | Bootloader | yes | |
| `ker` | `os` | OS kernel | yes | `smm` |
| `sinit` | `dr` | Authenticated code module launched by CPU | yes | |
| `mle` | `dr` | Measured launch environment | yes | `smm` in `P1`-`P4` / `stm` in `P5`|
| `stm` | `dr` | SMI transfer monitor | yes | |
| `app` | `usr` | The application being attested | yes | |


## Protocols

| Name | Protocol | Description |
| --- | --- | --- |
| `P1` | `ms(cpu,sinit) +<+ ms(sinit,mle) +<+ ms(mle,app)` | Dynamic |
| `P2` | `ms(crtm,bios) +<+ ms(bios,boot) +<+ ms(boot,ker) +<+ ms(ker,app)` | Static |
| `P3` | `ms(cpu,sinit) +<+ ms(sinit,mle) +<+ ms(sinit,smm) +<+ ms(mle,app)` | Dynamic. Measures `smm`. |
| `P4` | `ms(crtm,bios) +<+ ms(bios,boot) +<+ ms(bios,smm) +<+ ms(boot,ker) +<+ ms(ker,app)` | Static. Measures `smm`. |
| `P5` | `ms(cpu,sinit) +<+ ms(sinit,mle) +<+ ms(sinit,stm) +<+ ms(mle,app)` | Dynamic. Measures `stm`. |

There is no static counterpart to `P5`.

## Adversary ordering

Corrupting SMM is easier than any of the other measured component including STM.

`c(smm) <= c(bios),  c(smm) <= c(boot),  c(smm) <= c(ker),  c(smm) <= c(sinit),  c(smm) <= c(mle),  c(smm) <= c(stm)`


## Results

| Result | |
| --- | --- | 
| `P1 = P2` | Dynamic and static are the same |
| `P3 = P4` | Dynamic and static are the same |
| `P1 <= P3` | Measuring `smm` is an improvement |
| `P2 <= P4` | Measuring `smm` is an improvement |
| `P3 <= P5` | The `stm` is an improvement over measuring `smm` |

