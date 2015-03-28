// ************************************** SOCIAL NETWORK ******************************************* //

sig MyString {}

// social network is a set of interacting actors
// there is only one single social network
one sig SocialNetwork {
	actors: some Actor
}

// ************************************** ACTORS ******************************************* //

abstract sig Actor {
	id: one ID,
	contents: set Content
}

sig User extends Actor {
	friends: some User,
	follow: set Actor,
	block: set User,
	newsfeed: set Content
}

sig Group extends Actor {
	members: some User,
	admins: some User
}

sig ID {}

fact one_social_network {
	// all actors belong to the same social network
	all s: SocialNetwork | s.actors = Actor
}

fact unique_id {
	// ids are unique
	all disjoint a1, a2: Actor | a1.id != a2.id
}

fact friends {
	// friendships are mutual
	all u1, u2: User | u1 in u2.friends <=> u2 in u1.friends
}

fact not_in_own_lists {
	// user doesn't follow or block itself, and is not his own friend
	all u: User | u not in u.friends and u not in u.follow and u not in u.block
}

fact admins_are_members {
	// every admin has to be a member of the group
	all g: Group | g.admins in g.members
}

fact group_members_not_follow {
	// a group member doesn't follow the group
	all g: Group, m: g.members | g not in m.follow
}

// ************************************** CONTENT ******************************************* //

abstract sig Content {
	sender: one Actor,
	privacy: one Privacy,
	viewers: set User,
	modifiers: set User
}

abstract sig NonCommentable extends Content {}

// groups also have PersonalData (e.g. group name)
sig PersonalData extends NonCommentable {
	type: one MyString, // e.g. "Name"
	data: one MyString // e.g. "Rik"
}

sig Message extends NonCommentable {
	text: one MyString,
	photos: set Photo,
	receiver: one User
}

abstract sig Commentable extends Content {
	comments: set Comment
}

sig Post extends Commentable {
	text: MyString,
	photos: set Photo
}

sig Photo extends Commentable {}

sig Comment extends Commentable {
	text: one MyString,
	comment_on: one Commentable
}

fact receiver_sender {
	// don't send a message to yourself
	all m: Message | m.sender != m.receiver
}

fact no_group_messages {
	// groups can't send messages
	all m: Message | m.sender in User
}

fact acyclic_comments {
	// no cyclic comments
	no c: Comment | c in c.^comment_on
}

fact personal_data_type_unique {
	// the type of personal data is unique for a user. e.g.  one user cannot have 2 names or 2 birthdays
	all u: User, disjoint p1, p2: u.contents & PersonalData | p1.type != p2.type
}

fact photos_in_post_or_message { 
	// each photo in a post or message is visible at least to all the people that can view the post or message
	all p: Post, photo: p.photos | p.viewers in photo.viewers
	all m: Message, photo: m.photos | m.viewers in photo.viewers
}

fact comments_viewers {
	// each comment on a commentable content is visible at least to all the people that can view the content
	all comment: Comment, content: comment.comment_on | content.viewers in comment.viewers
}

// ************************************** PRIVACY ******************************************* //

// Pri = Private; Fri = Friends; FoF = Friends of Friends; Tra = Transitive Friends; Pub = Public
enum Privacy { Pri, Fri, FoF, Tra, Pub }
// this is the same as:
// abstract sig Privacy {}
// one sig Private, Friends, FriendsOfFriends, TransitiveFriends, Public

fact viewers {
	// privacy rules for content sent by users
	all c: Content, s: (c.sender & User) {c.viewers =
		s
		+ { u: s.friends | c.privacy in (Fri + FoF)} 
		+ { u: s.friends.friends | c.privacy in FoF}
		+ { u: s.^friends | c.privacy in Tra}
		+ { u: User | c.privacy in Pub}
		+ {m: c.receiver | c in Message}
		- s.block
	}
	// privacy rules for content sent by groups
	all c: Content, s: (c.sender & Group) {c.viewers = 
		{ u: User | c.privacy in Pub}
		+ { u: s.members |  c.privacy not in Pub}
	}
}

// ************************************** GENERAL FACTS ******************************************* //

fact newsfeed {
	// a content comes a a users newsfeed if the user is allowed to see it and
	// if the user follows the sender
	all u: User, c: Content | u in c.viewers and c.sender in u.follow <=> c in u.newsfeed
}

fact sender {
	// a content appears in the contents list of the sender
	all c: Content | c in c.sender.contents
}

fact unique_sender {
	// a message can only be sent by one actor
	all c: Content, disjoint a1, a2: Actor | not (c in a1.contents and c in a2.contents)
}

fact modifiers {
	// in case the sender of a content is a user, the modifier is the sender
	all c: Content, s: (c.sender & User) | c.modifiers = s
	// in case the sender iof a content is a group, the modifiers are the administrators
	all c: Content, s: (c.sender & Group) | c.modifiers = s.admins
}

// ************************************** TASK C ******************************************* //

// holds iff the given user can see the given content
pred canSee[user: User, content: Content] {
	user in content.viewers
}

// holds iff the given user is allowed to modify the given content
pred canModify[user: User, content: Content] {
	user in content.modifiers
}

// holds iff the user should see the content on his newsfeed
pred isOnNewsFeed[user: User, content: Content] {
	content in user.newsfeed
}

// ************************************** TASK D ******************************************* //

// 1. Comment chains are acyclic
assert d1 { no c: Comment | c in c.^comment_on }

// 2. A user can modify only content they can see
assert d2 { all u: User, c: Content | canModify[u, c] => canSee[u, c] }

// 3. A user can modify all the content they have created
assert d3 { all u: User, c: u.contents | u in c.modifiers }

// 4. If a post or message includes photos, the photos are visible at least to all the people that can view the post
assert d4 { all p: Post, photo: p.photos |  p.viewers in photo.viewers }
assert d4' { all m: Message, photo: m.photos | m.viewers in photo.viewers  }

// 5. Each group has members
assert d5 { all g: Group | some g.members }

// 6. A user’s newsfeed only has content visible to her
assert d6 { all u: User, c: u.newsfeed | canSee[u, c] }

// 7. A user cannot see any content created by a user that blocks them
assert d7 { all u: User, u': u.block, c: u.contents | not canSee[u', c] }


// ************************************** TASK E ******************************************* //

// 1. A comment chain that is 5 comments long
pred e1 {
	some c1,c2: Comment | c1.comment_on.comment_on.comment_on.comment_on = c2
}
// run e1 for 6

// 2. 3 users that form 7 different groups, each with a different set of members
pred e2 {
	#Group = 7
	#User = 3
	all disjoint g, g': Group | g.members != g'.members
}
// run e2 for 10

// 3. 4 users, where each has at least one friend, but not everyone is a transitive friend of everyone else
pred e3 {
	#User = 4
	all u: User | some u.friends
	some u: User | u.*friends != User
}
// run e3 for 4

// 4. A user that can see a post of a user that is a friend of friend (but not a direct friend), 
//     which has privacy level “friend of friend” and includes a photo from a fourth user
pred e4[post: Post, s:post.sender & User, m: s.friends, v: post.viewers + m.friends - s.friends - s, photo: Photo, u4: (photo.sender - s - m - v) & User] {
	post.privacy = FoF
	photo in post.photos
}
// run e4 for 4

// 5. A post that includes a photo created not by the poster, where the photo is not public
pred e5[post: Post, photo: post.photos] {
	post.sender != photo.sender
	post.sender in User
	photo.sender in User
	photo.privacy not in Pub
}
// run e5

// 6. A post with the privacy level “friends of friends”, which includes a photo created by a friend of the creator of the post. 
//     Some friend of the creator of the post must be able to see the post, but not the photo
pred e6[post: Post, photo: post.photos, u: post.sender.friends] {
	post.privacy in FoF
	photo.sender in post.sender.friends
	u in post.viewers - photo.viewers
}
// run e6 for 10 //-> No Instance found
// This is infeasible, it is in contradiction with property D4

pred show {}
run show for exactly 4 ID, exactly 2 Group, exactly 2 User, exactly 1 Message, 
	exactly 1 PersonalData, exactly 1 Comment, exactly 1 Photo, exactly 1 Post, exactly 2 MyString
