/* aquario_ctx
 * Author: agostinho
 * Creation date: 22/08/2022
 */
MACHINE
    aquario_ctx
SETS
    WATER_TYPES = {fresh, salt} ; SEX = {male,female} ; FISH_SPECIES = {general,nemo} ; LIGHT_MODE = {on,off} ; ALGAE_SPECIES = {common, anemona}; FISH_ID ; ALGAE_ID ; AQUARIUM_STATUS = {plancton_level, biological_waste}
CONSTANTS
    MAX_FISH,
    MAX_ALGAE,
    PROPORTIONS,
    SCHEDULER,
    RESTRICTIONS
//    water_type
    
PROPERTIES
    MAX_FISH : NAT
    & MAX_FISH > 1
    & MAX_ALGAE : NAT
    & MAX_ALGAE > 1
    & RESTRICTIONS = {general |-> common , nemo |-> anemona}
    // FOOD scheduler
    & SCHEDULER = {general |-> 2, nemo |-> 3}
    // PROPORTIONS contains the female ratio, the male is 1
    & PROPORTIONS : FISH_SPECIES +-> NAT
    & PROPORTIONS = {general |-> 1, nemo |-> 3}
    & card (FISH_ID) = 9
    & card (ALGAE_ID) = 10
//    & water_type : WATER_TYPES
END