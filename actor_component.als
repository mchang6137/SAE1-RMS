// every actor of the social network is identified by a unique id
sig ActorID {}

// social network is a set of interacting actors
// there is only one single social network
one sig SocialNetwork {
	actors: set ActorID
}

// ***************************** ACTORS **************************** //

// every actor (user / group) has an id and a list of allowed and blocked followers
abstract sig Actor {
	id: ActorID,
	allowedFollowers: set ActorID,
	blockedFollowers: set ActorID,
} {
	// actor doesn't follow or block itself
	id not in allowedFollowers && id not in blockedFollowers
	// a follower is either allowed or blocked
	no f: ActorID | f in allowedFollowers && f in blockedFollowers
}

sig PersonalProfile extends Actor {
	friends: set ActorID
} {
	// user is not it's own friend
	id not in friends
}

sig GroupProfile extends Actor {
	// every group has at least one group member and administrator
	groupMembers: some ActorID,
	administrators: some ActorID
} {
	// administrator must be group member
	no m: ActorID | m in administrators && m not in groupMembers
}


// ************************ CONSTRAINTS **************************** //

// no id exists outside the social network
fact {
	no i: ActorID, s: SocialNetwork | i not in s.actors
}

// IDs are unique
fact {
	all disj a1, a2: Actor | a1.id !=  a2.id
}

// every actor in the social network is either a user or a group
fact {
	#(SocialNetwork.actors) = # (PersonalProfile + GroupProfile)
}

// friendships are mutual
fact {
	all disj p1, p2: PersonalProfile | p1.id in p2.friends <=> p2.id in p1.friends
}

// groups have restricted functionality
fact {
	// groups cannot be friends
	no g: GroupProfile, p: PersonalProfile | g.id in p.friends
	// groups cannot follow users
    no g: GroupProfile, p: PersonalProfile | g.id in p.allowedFollowers || g.id in p.blockedFollowers
    // groups cannot follow groups
    no g1, g2: GroupProfile | g1.id in g2.allowedFollowers || g1.id in g2.blockedFollowers
	// groups cannot have membership or admin rights in groups
	no g1, g2: GroupProfile | g1.id in g2.groupMembers || g1.id in g2.administrators
}




pred show{}

run show
