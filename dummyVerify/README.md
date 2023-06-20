# Circuits

## Credential Registration

- Inputs:
  - wallet address pkW
  - audit token alpha
  - tracing token gamma
  - signature on tokens
- Operations:
  - Check signature
  - Compute token commitment and store it

## Credential Verification Circuit

- Static Public Inputs: 
  - CA's public key pkCA: 2 field elements
  - Auditors' public key pkA: 10 field elements
  - Root of revocation list rtrl: 1 field element
- User-specific Inputs:
  - wallet address pkW: 1 field element
  - token commitment nu: 32-bytes or 2 field elements
- Total inputs: 13 + 3
- no caching

## Batched Registration (L1)

- Inputs:
  - wallet addresses pkW_i
  - audit tokens alpha_i
  - tracing tokens gamma_i
  - signatures on tokens
- Operations:
  - same as credential registration
  - -21K gas for making a transaction

## Batched Verification Circuit (L1)

- Public Inputs to SNARK: 
  - CA's public key pkCA: 2 field elements
  - Auditors' public key pkA: 10 field elements
  - Root of revocation list rtrl: 1 field element
  - Commitment H: 32-bytes or 2 field elements
- Operations:
  - retrieve token commitments nu_i
  - hash wallets and nu_i's to get H
  - verify SNARK

## Batched Registration (L2)

- Public Inputs to SNARK:
  - state before: 1 field element
  - state after: 1 field element
  - commitment H: 32-bytes or 2 field elements
- Inputs to contract
  - new state
  - all tokens
  - all addresses
- Operations:
  - hash everything to get H
  - cache all 

## Batched Verification Circuit (L2)

- Public Inputs to SNARK:
  - CA's public key pkCA: 2 field elements
  - Auditors' public key pkA: 10 field elements
  - Root of revocation list rtrl: 1 field element
  - state before: 1 field element
  - state after: 1 field element
  - commitment H: 32-bytes or 2 field elements
- Inputs to contract
  - new state
  - all tokens
  - all addresses
- Operations:
  - hash everything to get H
  - cache all 