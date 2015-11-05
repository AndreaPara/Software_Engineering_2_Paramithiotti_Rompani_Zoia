//-------------------signature-----------------------------

abstract sig Person {}

abstract sig User extends Person {}

sig RegisteredUser extends User{

}

sig AuthenticatedUser extends RegisteredUser {
	
}

sig TaxiDriver extends Person {
	taxi: one Taxi
}

sig Taxi {

}

sig Queue {
	taxies: set Taxi
}

sig Zone {
	queue: one Queue
}

sig City {
	zones: set Zone
}

abstract sig Request {
	user: one AuthenticatedUser
}

sig NormalRequest extends Request {

}


sig Reservation extends Request {

}

sig SharedRequest extends Request {

}

sig PassengerInfo {
	user: one AuthenticatedUser
}

abstract sig Ride {
	taxi: one Taxi,
        passengers: some PassengerInfo // so no ride without info
}

sig NormalRide extends Ride {
	request: one NormalRequest
}

sig ReservedRide extends Ride {
	request:one Reservation
}

sig SharedRide extends Ride {
	requests: some SharedRequest
}

sig Skynet {
	registeredUsers:set RegisteredUser,
	city: one City,
	taxidrivers: set TaxiDriver,
	requests: set Request,
	normalRides: set NormalRide,
	sharedRides:set SharedRide,
	reservedRides:set ReservedRide
}

//-----------------------FACTS ---------------------------------------------




fact noTaxiDriversSameTaxi{
	no t1:TaxiDriver,t2:TaxiDriver| t1.taxi=t2.taxi && !(t1=t2)
}

fact noTaxiWithoutDriver{
	all tax:Taxi| one driver:TaxiDriver | driver.taxi=tax
}

fact noForeverAloneQueue {
	all q:Queue | one zon:Zone | zon.queue=q
}

fact noMoreThanTwentyTaxiPerZoneQueue {
	all q:Queue | #q.taxies =<20
}

fact noUbiquitaxi{
	all que1:Queue, que2:Queue | !(que1=que2) implies ((que1.taxies & que2.taxies) = none)
}

fact noForeverAloneZone {
	all z:Zone | one c:City | z in c.zones
} 

fact noMultipleNormalRequestsForUser {
	all r1:NormalRequest,r2:NormalRequest | !(r1=r2) implies !(r1.user=r2.user)
}

fact noMultipleSharedRequestsForUser {
	all r1:SharedRequest,r2:SharedRequest | !(r1=r2) implies !(r1.user=r2.user)
}

fact noNormalAndSharedRequestsForUserAtSameTime {
	all r1:SharedRequest,r2:NormalRequest | !(r1.user=r2.user)
}

fact noRideWithoutTaxi {
	all r:Ride | one t:Taxi | r.taxi=t
}

fact noTwoRidesWithSameTaxi {
	no r1:Ride, r2:Ride | r1.taxi =r2.taxi && !(r1=r2)
}

fact noPassengerInfoWithoutAssociatedRide {
	all p:PassengerInfo |one r:Ride | p in r.passengers
}
fact noMultiplePassengerInfoForSameAuthenticatedUser{
	all p1:PassengerInfo, p2:PassengerInfo | !(p1=p2) implies !(p1.user=p2.user)
}

fact noMultipleNormalRideWithSameRequest{
	all n1:NormalRide,n2:NormalRide | !(n1=n2) implies !(n1.request=n2.request) 
}

fact noMultipleReservedRideWithSameRequest{
	all rr1:ReservedRide,rr2:ReservedRide | !(rr1=rr2) implies !(rr1.request=rr2.request) 
}

fact noMultipleSharedRideWithSameSharedRequest{
	all sr1:SharedRide, sr2:SharedRide | !(sr1=sr2) implies !(sr1.request=sr2.request)
}

fact noNormalRideWithMultiplePassengersInfo{
	all n:NormalRide | #n.passengers=1
}
// un solo passeggero e che le info del passeggero che hanno sono quelle del passeggero della request
fact noNormalRideWithAPassengerInfoThatIsNotAPassenger{
	all n:NormalRide | all p:PassengerInfo | p in n.passengers implies p.user=n.request.user
}

fact noSharedRideWithAPassengerInfoThatIsNotAPassenger{
	all sr:SharedRide | all p:PassengerInfo |(p in sr.passengers)implies  p.user in sr.requests.user
}

fact noReservedRideWithAPassengerInfoThatIsNotAPassenger{
	all rr:ReservedRide | all p:PassengerInfo | p in rr.passengers implies p.user=rr.request.user
}

//--------------------------skynet controls everything---------------------
fact noNormalRideNotInSkynet {
	all r:NormalRide | one s:Skynet | r in s.normalRides
}
fact noSharedRideNotInSkynet {
	all r:SharedRide | one s:Skynet | r in s.sharedRides
}
fact noReservedRideNotInSkynet {
	all r:ReservedRide | one s:Skynet | r in s.reservedRides
}
fact noRequestNotInSkynet {
	all r:Request |one s:Skynet | r in s.requests
}

fact noRegisteredUserNotInSkynet {
	all r:RegisteredUser |one s:Skynet | r in s.registeredUsers
}





//------------------------------------PREDICATE-----------------------------------------------
pred show (){
	#Skynet=1
	#Zone<12
	#Taxi>5
	#City=1
	#AuthenticatedUser>2
	#Ride>2
}
run show for 11


//------------------------------------ASSERTS----------------------------------------------
assert noUbiquitaxi{
	all que1:Queue, que2:Queue | !(que1=que2) implies ((que1.taxies & que2.taxies) = none)
}
check noUbiquitaxi

assert oneSharedRideWithOneRide{
	all sr:SharedRide| #sr.requests=1
}
check oneSharedRideWithOneRide


