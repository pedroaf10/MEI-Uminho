package com.gamehub.Repositories;

import com.gamehub.Model.Posts.Post;
import org.springframework.data.repository.CrudRepository;

public interface PostRepository extends CrudRepository<Post, Integer> {
}
