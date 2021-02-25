MACHINE
    PaperRound
    
SETS
    NEWSPAPERS = { Guardian, Times, Telegraph, Daily_Mail, Financial_Times , empty_paper};
    MAGAZINES = { Vogue, Beano, Dandy, Hello, OK, empty_mag};
    ANSWER = { SUCCESS, FAILURE }
    
CONSTANTS
    HOUSES, MAX_MAGS

PROPERTIES
    HOUSES = 1..10 &
    MAX_MAGS = 3
    
VARIABLES
    paperset, magazineset,
    guardianstock, timesstock, telegraphstock, mailstock, ftstock,
    voguestock, beanostock, dandystock, hellostock, okstock,
    gotpapers 
    
INVARIANT
    paperset : HOUSES +-> NEWSPAPERS &
    magazineset : HOUSES <-> MAGAZINES &
    guardianstock : NAT & timesstock : NAT & telegraphstock: NAT & mailstock : NAT & ftstock : NAT &
    voguestock : NAT & beanostock : NAT & dandystock : NAT & hellostock : NAT & okstock : NAT &
    gotpapers <: HOUSES 
    
INITIALISATION
    paperset := HOUSES * { empty_paper } || magazineset := HOUSES * { empty_mag } ||
    guardianstock, timesstock, telegraphstock, mailstock, ftstock := 0, 0, 0, 0, 0 ||
    voguestock, beanostock, dandystock, hellostock, okstock := 0, 0, 0, 0, 0 ||
    gotpapers := {}

OPERATIONS
    
    ans <-- requestPaperDelivery( house, paper ) =
    PRE house : HOUSES & 
        paper : NEWSPAPERS & 
        paper /: { empty_paper } &
        ran( {house} <| paperset) = {empty_paper} 
    THEN
            IF ( paper : {Guardian} )
            THEN guardianstock := guardianstock + 1 ||
                 paperset( house ) := paper ||
                 gotpapers := gotpapers \/ {house} ||
                 ans := SUCCESS
            ELSIF ( paper : {Times})
            THEN timesstock := timesstock + 1 ||
                 paperset( house ) := paper ||
                 gotpapers := gotpapers \/ {house} ||
                 ans := SUCCESS
            ELSIF ( paper : {Telegraph})
            THEN telegraphstock := telegraphstock + 1 ||
                 paperset( house ) := paper ||
                 gotpapers := gotpapers \/ {house} ||
                 ans := SUCCESS
            ELSIF ( paper : {Daily_Mail})
            THEN mailstock := mailstock + 1 ||
                 paperset( house ) := paper ||
                 gotpapers := gotpapers \/ {house} ||
                 ans := SUCCESS
            ELSE ftstock := ftstock + 1 ||
                 paperset( house ) := paper ||
                 gotpapers := gotpapers \/ {house} ||
                 ans := SUCCESS
            END  
    END ;
    
    ans <-- cancelPaperDelivery( house ) =
    PRE house : HOUSES & 
        paperset(house) /= empty_paper &
        empty_mag : magazineset[{house}]
    THEN
        IF ( ran({ house } <| paperset) = {Guardian} )
            THEN guardianstock := guardianstock - 1 ||
                 paperset( house ) := empty_paper ||
                 gotpapers := gotpapers - { house } ||
                 ans := SUCCESS
                 
            ELSIF ( ran({ house } <| paperset) = {Times})
            THEN timesstock := timesstock - 1 ||
                 paperset( house ) := empty_paper ||
                 gotpapers := gotpapers - { house } ||
                 ans := SUCCESS
                 
            ELSIF ( ran({ house } <| paperset) = {Telegraph})
            THEN telegraphstock := telegraphstock - 1 ||
                 paperset( house ) := empty_paper ||
                 gotpapers := gotpapers - { house } ||
                 ans := SUCCESS
                 
            ELSIF ( ran({ house } <| paperset) = {Daily_Mail})
            THEN mailstock := mailstock - 1 ||
                 paperset( house ) := empty_paper ||
                 gotpapers := gotpapers - { house } ||
                 ans := SUCCESS
                 
            ELSE ftstock := ftstock - 1 ||
                 paperset( house ) := empty_paper ||
                 gotpapers := gotpapers - { house } ||
                 ans := SUCCESS
                 
            END  
    END;

    ans <-- requestMagazineDelivery( house, magazine ) =
    PRE 
        house : HOUSES &
        magazine : MAGAZINES & 
        paperset(house) /= empty_paper & 
        magazine /= empty_mag &
        magazine /: ran( {house} <| magazineset) & 
        card(magazineset[{house}]) < 3  
        
    THEN
        IF (empty_mag : ran( {house} <| magazineset))         
        THEN
            magazineset := magazineset <+ { house |-> magazine } ||
            ans := SUCCESS
        ELSE
            magazineset := magazineset \/ {house |-> magazine} ||
            ans := SUCCESS 
        END
        
    END;

    ans <-- cancelMagazineDelivery( house, magazine ) =
    PRE house : HOUSES &
        magazine : MAGAZINES &
        magazine /= empty_mag &
        card(magazineset[{house}]) >= 1  &
        magazine : ran( {house} <| magazineset) &
        paperset[{house}] /= {empty_paper}
    THEN
        IF (card(magazineset[{house}]) >= 2)
            THEN
                magazineset := magazineset - {house |-> magazine} ||
                ans := SUCCESS 
        ELSE
                magazineset := magazineset - {house |-> magazine} \/ {house |-> empty_mag} ||
                ans := SUCCESS 
                
                END
    END; 
    
    /* ENQUIRY OPERATIONS */

    ans <-- housesDeliveredTo =
        PRE
            card(gotpapers) >= 1
        THEN
            ans := gotpapers
        END;
        
    ans <-- whatPaperDeliveredTo( house ) =
        PRE
            house : HOUSES &
            paperset(house) /= empty_paper
        THEN
            ans := paperset( house )
        END;
 
    ans <-- whatMagazineDeliveredTo( house ) =
        PRE
            house : HOUSES &
            empty_mag /: ran({ house } <| magazineset)
        THEN
            ans := ran( {house} <| magazineset)
        END;
    
    ans <-- whatPapersSold = 
        PRE
            card(paperset) >= 1 &
            {empty_paper} /= ran(paperset)
        THEN
            ans := ran(paperset) - {empty_paper}
        END;

    ans <-- whatMagazinesSold =
        PRE
            card(magazineset) >= 1
        THEN
            ans := ran(magazineset) - {empty_mag}
        END;

    ans <-- papersSold(paper) =
    PRE
        paper : NEWSPAPERS &
        paper /: { empty_paper }
    THEN
        IF (paper = Guardian)
        THEN
            ans := guardianstock
        ELSIF (paper = Times)
        THEN
            ans := timesstock
        ELSIF (paper = Telegraph)
        THEN
            ans := telegraphstock
        ELSIF (paper = Daily_Mail) 
        THEN
            ans := mailstock
        ELSE
            ans:= ftstock
        END
END;

ans <-- magazinesSold( magazine ) =
    PRE
        magazine : MAGAZINES &
        magazine /= empty_mag
    THEN
        IF (magazine = Vogue)
        THEN
            ans := voguestock
        ELSIF (magazine = Beano)
        THEN
            ans := beanostock
        ELSIF (magazine = Dandy)
        THEN
            ans := dandystock
        ELSIF (magazine = Hello)
        THEN
            ans := hellostock
        ELSE
            ans := okstock
        END
    END

/* End of Operations */
END