-- StoreClient:	either a guest or a customer
abstract sig StoreClient{}

-- Guest:	a store client that uses CLup through the PTD
sig Guest extends StoreClient{}

-- Customer:	a store client that uses CLup through the Application
sig Customer extends StoreClient{
    -- notifications:   the notifications received from CLup
    notifications: set Notification
}

-- SlotStatus:		the status of a slot
abstract sig SlotStatus{}

-- Available:	the slot can still be assigned to a store client
lone sig Available extends SlotStatus{}

-- Unavailable:	the slot cannot be assigned. Maximum capacity has been reached.
lone sig Unavailable extends SlotStatus{}

-- Slot:	a specific day/time range for a specific store. Without loss of generality, they represent only pre-defined and non-overlapping day/time slots. Indeed, we can imagine that any longer slot is obtained by reserving more slots of fixed duration.
sig Slot{
    -- status: 	the status of the slot
    status: one SlotStatus
}

-- Department:	a department of a store
sig Department{
    -- capacity:	the maximum capacity of the department
    capacity: one Int
}{
    -- The capacity of each department must be > 0
    capacity > 0
}

-- Store:	a registered store
sig Store{
    -- storeId:		an identifier for the Store
    storeId: one StoreId,
    -- departments: the set of all the departments of the Store
    departments: some Department,
    -- visits:	a set of all the scheduled shop visits. A visit is scheduled when it is booked or requested by a client.
    visits: set Visit,
    -- clientsInside:	the number of clients currently inside the store
    clientsInside: set StoreClient,
    -- currentSlot:	the current day/time slot for the Store
    currentSlot: one Slot,
    -- storeSlots:	set of all the day/time slots of the Store
    storeSlots: some Slot
}{
    -- The current slot must be a slot related to the store
    currentSlot in storeSlots

    -- The visits must be scheduled for a slot related to the store
    visits.slot in storeSlots
}

-- Visit:	scheduled visit to a store of a StoreClient. It may have been requested through the "Book a Visit", "Line Up from App" or "Line Up from PTD" functionality
sig Visit{
    -- slot:	the assigned slot
    slot: one Slot,
    -- qrCode:		the assigned QR code 
    qrCode: one QrCode,
    -- reservationId:	the assigned identifier of the visit
    reservationId: one ReservationId,
    -- visitedDepartments:	the list containing all the departments visited. 
    visitedDepartments: some Department,
    -- storeClient:	the StoreClient to whom the visit is assigned
    storeClient: one StoreClient
}{
    -- Every visit must be related to at least one department
    #visitedDepartments > 0
}

-- Notification:	a notification sent by CLup suggesting a slot to a Customer
sig Notification{
    -- suggestedSlot:	the suggested slot
    suggestedSlot: one Slot
}{
    -- The suggested slots must be available
    suggestedSlot.status in Available
}

-- QrCode:	the QR code assigned to a visit to a Store
sig QrCode{}

-- Id:  a generic identifier
abstract sig Id{}
sig ReservationId extends Id{}
sig StoreId extends Id{}

-- -- -- -- -- -- -- -- -- -- -- -- 
-- -- -- F  A  C  T  S  -- -- -- -- 
-- -- -- -- -- -- -- -- -- -- -- -- 

-- There is no SlotStatus not associated with any Slot 
fact noSlotStatusWithoutSlot{
    all ss: SlotStatus | some sl: Slot | sl.status=ss
}

-- Every Slot is associated with one and only one Store
fact slotBelongsToAStore{
    all sl: Slot | one s: Store | sl in s.storeSlots
}

-- Every Visit is associated with one and only one Store  
fact visitBelongsToAStore{
    all v: Visit | one s: Store | v in s.visits
}

-- There is no Notification not associated with any Customer  
fact noNotificationWithoutCustomer{
    all n: Notification | some c: Customer | n in c.notifications
}

-- Every Department is associated with at least one Store  
fact departmentBelognsToAStore{
    all d: Department | some s: Store | d in s.departments
}

-- Every QrCode is associated with one and only one Visit
fact qrCodeBelongsToAVisit{
    all qr: QrCode | one v: Visit | v.qrCode = qr
}

-- Every reservationId is associated with one and only one visit
fact reservationIdBelongsAToVisit{
    all id: ReservationId | one v: Visit | v.reservationId = id
}

-- Every storeId is associated with one and only one store
fact storeIdBelongsToAStore{
    all id: StoreId | one s: Store | s.storeId = id
}

-- Every Guest is supposed to visit all the departments of a store since he cannot -- specify them
fact guestVisitAllDepartments{
all s: Store | all v: s.visits | ((v.storeClient in Guest) implies (s.departments = v.visitedDepartments))
}

-- All the Departments of a Visit belongs to the selected Store
fact visitedDepartmentsRelatedToSameStore{
    all s: Store | all v: s.visits | all d: v.visitedDepartments | d in s.departments
}

-- A slot is available iff there exists at least one department of the store that is -- not full for that day/time slot.
fact slotAvailability{
    all s: Store | all sl: s.storeSlots| (sl.status = Available) iff 
	( some d: s.departments | 
        #{ v: s.visits| v.slot = sl and d in v.visitedDepartments} < d.capacity
    )
}

-- The capacity limit of the departments must always be respected
fact noVisitsOverCapacity{
    all s: Store | all sl: s.storeSlots| all d: s.departments |
    (#{ v: s.visits| v.slot = sl and d in v.visitedDepartments} <= d.capacity)
}

-- The same StoreClient cannot reserve the same slot more than once
fact scheduleVisitOnlyOnceForSameSlot{
    all sc: StoreClient | no disj v1,v2: Visit | 
    (v1.storeClient = sc and v2.storeClient = sc and v1.slot = v2.slot)
}

-- There is no StoreClient inside a Store without a scheduled Visit for the
-- currentSlot.
fact noStoreClientInsideAStoreWithoutVisit{
    all s: Store | all sc: s.clientsInside |
    (some v: s.visits | v.storeClient = sc and v.slot = s.currentSlot)
}

-- Customers receive suggestions for slots they have not already booked
fact notifyOnlyNonBooked{
    all c: Customer | all n: c.notifications | no v: Visit | v.storeClient = c and v.slot = n.suggestedSlot
}

-- There are no multiple notifications for the same slot
fact notifyOnlyOnce{
    all disj n1,n2: Notification | n1.suggestedSlot != n2.suggestedSlot
}

-- No suggestion refers to the currentSlot of the store
fact notifyInAdvance{
    all s: Store| all n: Notification | not (n.suggestedSlot = s.currentSlot)
}

-- The notifications’ suggestions, being based on the Customer's habits, are 
-- related to stores that the Customer has already visited 
fact notifyBasedOnHabits{
    all s: Store | all c: Customer | all sl: c.notifications.suggestedSlot | 
     sl in s.storeSlots implies (some v: s.visits | v.storeClient = c)
}

-- Guests can only request one visit
fact guestsAreNotRegistered{
	    all disj v1,v2: Visit | (v1.storeClient in Guest and v2.storeClient in Guest) 
    implies v1.storeClient != v2.storeClient
}

-- StoreClients cannot be inside more than one stores
fact storeClientInsideAtMostOneStore{
	    all disj s1,s2: Store | all sc: StoreClient | 
    (sc in s1.clientsInside implies not sc in s2.clientsInside)
}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- --  A  S  S  E  R  T  I  O  N  S -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

-- No crowded stores
assert noCrowdedStores{
    all s: Store | no sl: s.storeSlots | some  d: Department |
    (#{ v: Visit | v.slot = sl and d in v.visitedDepartments } > d.capacity)
}
--check noCrowdedStores for 10

-- No unscheduled StoreClients
assert noUnscheduledStoreClientsInside{
    no s: Store | some sc: s.clientsInside |  no v: s.visits | 
    (v.storeClient = sc and v.slot = s.currentSlot)
}
--check noUnscheduledStoreClientsInside for 10

-- Notifications relates to free slot not yet booked by the Customer
assert usefulNotifications{
	    all c: Customer | no n: c.notifications | (n.suggestedSlot.status = Unavailable)

    all s: Store | all v: s.visits| no sl: v.slot | 
    (sl in v.storeClient.notifications.suggestedSlot)
}
--check usefulNotifications for 10

-- Every reservationID uniquely identifies a scheduled visit
assert uniqeuReservationID{
    all disj v1,v2: Visit | v1.reservationId != v2.reservationId
}
--check uniqeuReservationID for 10

-- Every qrCode is unique
assert uniqueQrCode{
    all disj v1,v2: Visit | v1.qrCode != v2.qrCode
}
--check uniqueQrCode for 10

-- Every storeID uniquely identifies a Store
assert uniqeuStoreID{
    all disj s1,s2: Store | s1.storeId != s2.storeId
}
--check uniqeuStoreID for 10
