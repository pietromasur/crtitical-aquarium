/* aquario
 * Author: agostinho
 * Creation date: 22/08/2022
 */
MACHINE
    aquario
SEES
    aquario_ctx
VARIABLES
    fishes, 
    algae,
    light,
    aquarium_cycle,
     //Mover para variables
    bio_waste,
    plancton,
    //Usar boleanos para controle de operaçoes (ciclos)
    common_food_scheduler,
    nemo_food_scheduler,
    has_feed_common,
    has_feed_nemo,
    food_table,
    boolean_maplet, 
    aquarium_empty
    
INVARIANT
    //Alimentar usando set comprehension
    // 
    fishes : FISH_ID +-> struct (f_species: FISH_SPECIES, sex : SEX)
    & fishes : FIN(fishes)
    & algae : ALGAE_ID +-> struct (a_species: ALGAE_SPECIES)
    & algae : FIN(algae)
    & light : LIGHT_MODE +-> NAT
    & aquarium_cycle : NATURAL
    & card(dom(fishes)) <= MAX_FISH
    & card(algae) <= MAX_ALGAE
    & bio_waste : NAT & bio_waste <= 5
    & plancton : NAT & plancton <= 3
    & common_food_scheduler : NAT
    & nemo_food_scheduler : NAT
    & has_feed_common : NAT
    & has_feed_nemo : NAT
    & food_table : FISH_SPECIES +-> NAT
    & boolean_maplet : BOOL +-> NAT
    & aquarium_empty : BOOL
INITIALISATION
    aquarium_cycle := 0
    || fishes := {}    
    || algae := {}
    || light := {off |-> 0 , on |-> 1}
    || bio_waste := 0
    || plancton := 0
    || common_food_scheduler := SCHEDULER(general)
    || nemo_food_scheduler := SCHEDULER(nemo)
    || has_feed_common := 1
    || has_feed_nemo := 1
    || food_table := {general |-> 1, nemo |-> 1}
    || boolean_maplet := {FALSE |-> 1 , TRUE |->0}
    || aquarium_empty := TRUE
OPERATIONS
    add_fishes(fid, fs, ss) =
        // A fish can only be added if it's necessary algae is present on the aquarium
        PRE
            fid : FISH_ID
            & (card(dom(fishes)) < MAX_FISH)
            & fid /: dom(fishes)
            & fs : FISH_SPECIES
            & ss : SEX
            & rec (a_species : RESTRICTIONS(fs)) : ran(algae)
            & (food_table(fs) = 1)
        THEN
            fishes := fishes \/ {fid |-> rec(f_species: fs, sex :ss)}
            || aquarium_empty := FALSE
    END
    ;
    add_algae(aid, as) =
        PRE
            aid : ALGAE_ID
            & card(algae) < MAX_ALGAE
            & aid /: dom(algae)
            & as : ALGAE_SPECIES
        THEN
            algae := algae \/ {aid |-> rec(a_species: as)}
    END    
    ;
    rm_fish (fid) =
        PRE
            fid : FISH_ID
            & fid : dom(fishes)
            & (food_table((fishes(fid))'f_species)) = 1
        THEN
            fishes := {fid} <<|fishes
    END
    ;
    rm_algae (aid) =
        // An algae can only be removed if there is no fish depending on it or if there's more than one of it's kind
        PRE
            aid : ALGAE_ID
            & aid : dom(algae)
            & (card({rr | rr : ran(algae) & rr'a_species = (algae(aid))'a_species}) > 1 or card({ff | ff : ran (fishes) & RESTRICTIONS(ff'f_species) = (algae(aid))'a_species}) = 0)
            
        THEN
            algae := {aid} <<| algae
        END
    ;
    cycle_aquarium =
        BEGIN
            ASSERT
//                 a cycle can only be made if the fish species proportions are being obeyed
//                 Fish proportion
                (PROPORTIONS(general) * card({fid | fid : dom(fishes) & (fishes(fid))'f_species = general & (fishes(fid))'sex = male}) + 1) = (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = general & (fishes(fid))'sex = female}) + 1)
                & PROPORTIONS(nemo) * (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = nemo & (fishes(fid))'sex = male}) + 1) = (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = nemo & (fishes(fid))'sex = female}) + 3)
//                Food scheduler                    
                & (((common_food_scheduler mod SCHEDULER(general)) /= 0)  or (card({ff | ff : ran(fishes) & ff'f_species = general}) = 0) or has_feed_common = 0)
                & (((nemo_food_scheduler mod SCHEDULER(nemo)) /= 0) or (card({ff | ff : ran(fishes) & ff'f_species = nemo}) = 0) or has_feed_nemo = 0)
                // Plancton controller
               & (not (light(on) = 0) or plancton<3)
               & (not (light(off) = 0) or plancton>0)
               // Bio Waste controller
               & bio_waste < 4 
            THEN
                aquarium_cycle := aquarium_cycle+1 
                || common_food_scheduler := common_food_scheduler + (card({ff | ff : ran(fishes) & ff'f_species = general}) / 2)
                || nemo_food_scheduler := nemo_food_scheduler + (card({ff | ff : ran(fishes) & ff'f_species = nemo}) / 2)
                || has_feed_common := 1
                || has_feed_nemo := 1
                || plancton := plancton + light(off) - light(on)
                || bio_waste := bio_waste + boolean_maplet(aquarium_empty)
        END
    END
    ;
    feed_common = 
        PRE
            card({ff | ff : ran(fishes) & ff'f_species = general}) > 0
            & common_food_scheduler mod SCHEDULER(general) = 0
            & has_feed_common /= 0
            & (PROPORTIONS(general) * card({fid | fid : dom(fishes) & (fishes(fid))'f_species = general & (fishes(fid))'sex = male}) + 1) = (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = general & (fishes(fid))'sex = female}) + 1)
        THEN
            has_feed_common := 0 
            || common_food_scheduler := common_food_scheduler - SCHEDULER(general)
            || food_table := {general |-> 0, nemo |-> has_feed_nemo}
        END   
    ;
    feed_nemo = 
        PRE 
            card({ff | ff : ran(fishes) & ff'f_species = nemo}) > 0
            & nemo_food_scheduler mod SCHEDULER(nemo) = 0
            & has_feed_nemo /= 0
            & PROPORTIONS(nemo) * (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = nemo & (fishes(fid))'sex = male}) + 1) = (card({fid | fid : dom(fishes) & (fishes(fid))'f_species = nemo & (fishes(fid))'sex = female}) + 3)
        THEN
            has_feed_nemo := 0
            || nemo_food_scheduler := nemo_food_scheduler - SCHEDULER(nemo)
            || food_table := {general |-> has_feed_common, nemo |-> 0}
        END 
    ;
    turn_light_on = 
        PRE
            light(off) = 0
        THEN
            light := {off |-> 1, on |-> 0}
        END
    ;
    turn_light_off = 
        PRE
            light(on) = 0
        THEN 
            light := {off |-> 0, on |-> 1}
        END
    ;
    clean_aquarium = 
        PRE 
            bio_waste > 3
        THEN
            bio_waste := 1
        END        
    ;
    aquarium_status <-- get_status = aquarium_status := {plancton_level |-> plancton, biological_waste |-> bio_waste}
END
