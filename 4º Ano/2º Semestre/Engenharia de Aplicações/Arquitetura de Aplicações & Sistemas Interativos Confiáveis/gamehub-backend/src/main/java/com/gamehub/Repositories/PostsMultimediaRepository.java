package com.gamehub.Repositories;


import com.gamehub.Model.Posts.PostMultimedia;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.math.BigInteger;
import java.util.List;

public interface PostsMultimediaRepository extends CrudRepository<PostMultimedia, Integer> {

    String Find_Posts_Jogo = "SELECT * FROM post_multimedia WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY datetime DESC LIMIT 10 OFFSET :pagina";

    String Find_Posts_Jogo_data_asc = "SELECT * FROM post_multimedia WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY datetime ASC LIMIT 10 OFFSET :pagina";

    String Find_Posts_Jogo_data_desc = "SELECT * FROM post_multimedia WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY datetime DESC LIMIT 10 OFFSET :pagina";

    String Find_Posts_Jogo_likes_asc = "SELECT * FROM post_multimedia WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY likes ASC LIMIT 10 OFFSET :pagina";

    String Find_Posts_Jogo_likes_desc = "SELECT * FROM post_multimedia WHERE jogo in (SELECT nome FROM jogo WHERE id=:id_jogo) ORDER BY likes DESC LIMIT 10 OFFSET :pagina";

    String getPostsMultimediaGamer = "SELECT * FROM post_multimedia WHERE gamer_id=:id_gamer ORDER BY datetime DESC LIMIT 10 OFFSET :pagina";

    String likePost = "INSERT INTO likes VALUES ( :id_gamer , :id_post)";
    String updatelikesPost = "UPDATE post_multimedia SET likes = likes + 1 WHERE id=:id_post";
    String removeDislike = "DELETE FROM dislikes WHERE gamer=:id_gamer AND post=:id_post";

    String dislikePost = "INSERT INTO dislikes (gamer,post) VALUES ( :id_gamer , :id_post)";
    String updatedislikesPost = "UPDATE post_multimedia SET likes = likes - 1 WHERE id=:id_post";
    String removeLike = "DELETE FROM likes WHERE gamer=:id_gamer AND post=:id_post";


    String getLike = "SELECT EXISTS (SELECT * FROM likes WHERE gamer=:id_gamer AND post=:id_post)";

    String getDislike = "SELECT EXISTS (SELECT * FROM dislikes WHERE gamer=:id_gamer AND post=:id_post)";

    String deleteLikesFromPost = "DELETE FROM likes WHERE post=:id_post";

    String deleteDislikesFromPost = "DELETE FROM dislikes WHERE post=:id_post";

    String deletePostMultimediaTags = "DELETE FROM post_multimedia_tags WHERE post_multimedia_id=:id_post";

    String getPostsMultimediaTOP = "SELECT * FROM post_multimedia ORDER BY  DATE(datetime) DESC, likes DESC LIMIT :limit";

    String getTodosPostsMultimedia = "SELECT * FROM post_multimedia";


    @Query(value = Find_Posts_Jogo, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaJogo(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Query(value = Find_Posts_Jogo_data_asc, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaJogoDataAsc(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Query(value = Find_Posts_Jogo_data_desc, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaJogoDataDesc(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Query(value = Find_Posts_Jogo_likes_asc, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaJogoLikesAsc(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Query(value = Find_Posts_Jogo_likes_desc, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaJogoLikesDesc(@Param("id_jogo") int id_jogo, @Param("pagina") int pagina);

    @Modifying
    @Query(value = likePost, nativeQuery = true)
    @Transactional
    void likePost(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);

    @Modifying
    @Query(value = updatelikesPost, nativeQuery = true)
    @Transactional
    void update_likesPost(@Param("id_post") int id_post);

    @Modifying
    @Query(value = removeDislike, nativeQuery = true)
    @Transactional
    void removeDislikePost(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);

    @Modifying
    @Query(value = removeLike, nativeQuery = true)
    @Transactional
    void removeLikePost(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);


    @Modifying
    @Query(value = dislikePost, nativeQuery = true)
    @Transactional
    void dislikePost(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);

    @Modifying
    @Query(value = updatedislikesPost, nativeQuery = true)
    @Transactional
    void update_dislikesPost(@Param("id_post") int id_post);

    @Query(value = getLike, nativeQuery = true)
    BigInteger getLike(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);

    @Query(value = getDislike, nativeQuery = true)
    BigInteger getDislike(@Param("id_post") int id_post, @Param("id_gamer") int id_gamer);

    @Query(value = getPostsMultimediaGamer, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaGamer(@Param("id_gamer") int id_gamer, @Param("pagina") int pagina);


    @Modifying
    @Query(value = deleteLikesFromPost, nativeQuery = true)
    @Transactional
    void deleteLikesFromPost(@Param("id_post") int id_post);

    @Modifying
    @Query(value = deleteDislikesFromPost, nativeQuery = true)
    @Transactional
    void deleteDislikesFromPost(@Param("id_post") int id_post);

    @Modifying
    @Query(value = deletePostMultimediaTags, nativeQuery = true)
    @Transactional
    void deletePostMultimediaTags(@Param("id_post") int id_post);

    @Query(value = getPostsMultimediaTOP, nativeQuery = true)
    List<PostMultimedia> getPostsMultimediaTOP(@Param("limit") int limit);

    @Query(value = getTodosPostsMultimedia, nativeQuery = true)
    List<PostMultimedia> getTodosPostsMultimedia();
}
