// every actor of the social network is identified by a unique id
// users and groups have different capabilities, therefore treat them separately
abstract sig ActorID {}
sig UserID, GroupID extends ActorID {}

// social network is a set of interacting actors
// there is only one single social network
one sig SocialNetwork {
	actors: set ActorID
}

// ***************************** ACTORS **************************** //

// every actor (user / group) has a list of allowed and blocked followers
abstract sig Actor {
	allowedFollowers: set UserID,
	blockedFollowers: set UserID,
} {
	// a follower is either allowed or blocked
	no f: UserID | f in allowedFollowers && f in blockedFollowers
}

sig PersonalProfile extends Actor {
	id: UserID,
	friends: set UserID
} {
	// user is not it's own friend
	id not in friends
	// user doesn't follow or block itself
	id not in allowedFollowers && id not in blockedFollowers
}

sig GroupProfile extends Actor {
	id: GroupID,
	// every group has at least one group member and administrator
	groupMembers: some UserID,
	administrators: some UserID
} {
	// administrator must be group member
	no m: UserID | m in administrators && m not in groupMembers
}


// ************************ CONSTRAINTS **************************** //

// no id exists outside the social network
fact {
	no uid: UserID, s: SocialNetwork | uid not in s.actors
	no gid: GroupID, s: SocialNetwork | gid not in s.actors
}

// IDs are unique
fact {
	all disj p1, p2: PersonalProfile | p1.id !=  p2.id
	all disj g1, g2: GroupProfile | g1.id != g2.id
}

// every actor in the social network is either a user or a group
fact {
	#(SocialNetwork.actors) = # (PersonalProfile + GroupProfile)
}

// friendships are mutual
fact {
	all disj p1, p2: PersonalProfile | p1.id in p2.friends <=> p2.id in p1.friends
}




pred show{}
run show
