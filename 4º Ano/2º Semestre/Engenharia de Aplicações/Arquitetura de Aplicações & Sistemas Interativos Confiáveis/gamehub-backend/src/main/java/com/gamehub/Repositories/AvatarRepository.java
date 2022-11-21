package com.gamehub.Repositories;


import com.gamehub.Model.Users.Avatar;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

public interface AvatarRepository extends CrudRepository<Avatar, Integer> {
    String deleteAvatarGamer = "delete a.* from avatar as a" +
            " join gamer as g on a.id = g.avatar_id" +
            " where g.id = :id";


    String deleteAvatar = "delete from avatar where id = :id";

    @Modifying
    @Query(value = deleteAvatarGamer, nativeQuery = true)
    @Transactional
    void deleteAvatarGamer(@Param("id") int id);

    @Modifying
    @Query(value = deleteAvatar, nativeQuery = true)
    @Transactional
    void deleteAvatar(@Param("id") int id);
}
